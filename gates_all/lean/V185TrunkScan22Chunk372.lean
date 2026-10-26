import V185TrunkScan22Chunk371

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3317366 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_3317366 : Nat := 118140960795 + 3317366 * 2 ^ 59
def prefixEnd_3317366 : Nat := 4983230072969 + 3 ^ 40 * 3317366 * 2
def baseEnd_3317366 : Nat := 378534058862927338659715

theorem tailTrace_3317366 : CollatzResearch.WordTrace tailWord_3317366 prefixEnd_3317366 378534058862927338659715 := by
  unfold tailWord_3317366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562142381234813615730247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80662852066504678567789301 7562142381234813615730247)
  ·
    refine ⟨11343213571852220423595371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7562142381234813615730247 11343213571852220423595371)
    ·
      refine ⟨17014820357778330635393057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11343213571852220423595371 17014820357778330635393057)
      ·
        refine ⟨12761115268333747976544793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17014820357778330635393057 12761115268333747976544793)
        ·
          refine ⟨9570836451250310982408595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12761115268333747976544793 9570836451250310982408595)
          ·
            refine ⟨14356254676875466473612893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570836451250310982408595 14356254676875466473612893)
            ·
              refine ⟨5383595503828299927604835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14356254676875466473612893 5383595503828299927604835)
              ·
                refine ⟨8075393255742449891407253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383595503828299927604835 8075393255742449891407253)
                ·
                  refine ⟨378534058862927338659715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8075393255742449891407253 378534058862927338659715)
                  ·
                    rfl

theorem cell22_3317366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_3317366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317366 prefixEnd_3317366 := by exact prefixLift 3317366
  have htrace : WordTrace (prefixWord ++ tailWord_3317366) baseStart_3317366 baseEnd_3317366 := by
    simpa [prefixWord, tailWord_3317366, baseEnd_3317366] using wordTrace_append hprefix tailTrace_3317366
  have hstable : (prefixWord ++ tailWord_3317366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317366).length < 2 ^ (prefixWord ++ tailWord_3317366).sum := by decide
  have hdescent : baseEnd_3317366 < baseStart_3317366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317381 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_3317381 : Nat := 118140960795 + 3317381 * 2 ^ 59
def prefixEnd_3317381 : Nat := 4983230072969 + 3 ^ 40 * 3317381 * 2
def baseEnd_3317381 : Nat := 1135607311395326976854099

theorem tailTrace_3317381 : CollatzResearch.WordTrace tailWord_3317381 prefixEnd_3317381 1135607311395326976854099 := by
  unfold tailWord_3317381
  simp only [CollatzResearch.WordTrace]
  refine ⟨120994825194702675413479997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80663216796468450275653331 120994825194702675413479997)
  ·
    refine ⟨45373059448013503280054999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120994825194702675413479997 45373059448013503280054999)
    ·
      refine ⟨68059589172020254920082499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45373059448013503280054999 68059589172020254920082499)
      ·
        refine ⟨102089383758030382380123749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68059589172020254920082499 102089383758030382380123749)
        ·
          refine ⟨19141759454630696696273203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102089383758030382380123749 19141759454630696696273203)
          ·
            refine ⟨28712639181946045044409805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19141759454630696696273203 28712639181946045044409805)
            ·
              refine ⟨10767239693229766891653677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28712639181946045044409805 10767239693229766891653677)
              ·
                refine ⟨4037714884961162584370129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10767239693229766891653677 4037714884961162584370129)
                ·
                  refine ⟨3028286163720871938277597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037714884961162584370129 3028286163720871938277597)
                  ·
                    refine ⟨1135607311395326976854099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028286163720871938277597 1135607311395326976854099)
                    ·
                      rfl

theorem cell22_3317381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_3317381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317381 prefixEnd_3317381 := by exact prefixLift 3317381
  have htrace : WordTrace (prefixWord ++ tailWord_3317381) baseStart_3317381 baseEnd_3317381 := by
    simpa [prefixWord, tailWord_3317381, baseEnd_3317381] using wordTrace_append hprefix tailTrace_3317381
  have hstable : (prefixWord ++ tailWord_3317381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317381).length < 2 ^ (prefixWord ++ tailWord_3317381).sum := by decide
  have hdescent : baseEnd_3317381 < baseStart_3317381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317392 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_3317392 : Nat := 118140960795 + 3317392 * 2 ^ 59
def prefixEnd_3317392 : Nat := 4983230072969 + 3 ^ 40 * 3317392 * 2
def baseEnd_3317392 : Nat := 1135611076920126614829065

theorem tailTrace_3317392 : CollatzResearch.WordTrace tailWord_3317392 prefixEnd_3317392 1135611076920126614829065 := by
  unfold tailWord_3317392
  simp only [CollatzResearch.WordTrace]
  refine ⟨60497613198831412146065215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80663484265108549528086953 60497613198831412146065215)
  ·
    refine ⟨90746419798247118219097823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60497613198831412146065215 90746419798247118219097823)
    ·
      refine ⟨136119629697370677328646735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90746419798247118219097823 136119629697370677328646735)
      ·
        refine ⟨204179444546056015992970103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136119629697370677328646735 204179444546056015992970103)
        ·
          refine ⟨306269166819084023989455155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204179444546056015992970103 306269166819084023989455155)
          ·
            refine ⟨459403750228626035984182733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306269166819084023989455155 459403750228626035984182733)
            ·
              refine ⟨172276406335734763494068525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459403750228626035984182733 172276406335734763494068525)
              ·
                refine ⟨64603652375900536310275697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172276406335734763494068525 64603652375900536310275697)
                ·
                  refine ⟨48452739281925402232706773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64603652375900536310275697 48452739281925402232706773)
                  ·
                    refine ⟨1135611076920126614829065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48452739281925402232706773 1135611076920126614829065)
                    ·
                      rfl

theorem cell22_3317392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_3317392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317392 prefixEnd_3317392 := by exact prefixLift 3317392
  have htrace : WordTrace (prefixWord ++ tailWord_3317392) baseStart_3317392 baseEnd_3317392 := by
    simpa [prefixWord, tailWord_3317392, baseEnd_3317392] using wordTrace_append hprefix tailTrace_3317392
  have hstable : (prefixWord ++ tailWord_3317392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317392).length < 2 ^ (prefixWord ++ tailWord_3317392).sum := by decide
  have hdescent : baseEnd_3317392 < baseStart_3317392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317439 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 5]
def baseStart_3317439 : Nat := 118140960795 + 3317439 * 2 ^ 59
def prefixEnd_3317439 : Nat := 4983230072969 + 3 ^ 40 * 3317439 * 2
def baseEnd_3317439 : Nat := 378542388660211386301307

theorem tailTrace_3317439 : CollatzResearch.WordTrace tailWord_3317439 prefixEnd_3317439 378542388660211386301307 := by
  unfold tailWord_3317439
  simp only [CollatzResearch.WordTrace]
  refine ⟨120996940628492551319091371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80664627085661700879394247 120996940628492551319091371)
  ·
    refine ⟨181495410942738826978637057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120996940628492551319091371 181495410942738826978637057)
    ·
      refine ⟨136121558207054120233977793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181495410942738826978637057 136121558207054120233977793)
      ·
        refine ⟨102091168655290590175483345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136121558207054120233977793 102091168655290590175483345)
        ·
          refine ⟨76568376491467942631612509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102091168655290590175483345 76568376491467942631612509)
          ·
            refine ⟨28713141184300478486854691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76568376491467942631612509 28713141184300478486854691)
            ·
              refine ⟨43069711776450717730282037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28713141184300478486854691 43069711776450717730282037)
              ·
                refine ⟨4037785479042254787213941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43069711776450717730282037 4037785479042254787213941)
                ·
                  refine ⟨378542388660211386301307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4037785479042254787213941 378542388660211386301307)
                  ·
                    rfl

theorem cell22_3317439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 5].length) (baseStart_3317439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317439 prefixEnd_3317439 := by exact prefixLift 3317439
  have htrace : WordTrace (prefixWord ++ tailWord_3317439) baseStart_3317439 baseEnd_3317439 := by
    simpa [prefixWord, tailWord_3317439, baseEnd_3317439] using wordTrace_append hprefix tailTrace_3317439
  have hstable : (prefixWord ++ tailWord_3317439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317439).length < 2 ^ (prefixWord ++ tailWord_3317439).sum := by decide
  have hdescent : baseEnd_3317439 < baseStart_3317439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317454 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3317454 : Nat := 118140960795 + 3317454 * 2 ^ 59
def prefixEnd_3317454 : Nat := 4983230072969 + 3 ^ 40 * 3317454 * 2
def baseEnd_3317454 : Nat := 1135632300787179119778875

theorem tailTrace_3317454 : CollatzResearch.WordTrace tailWord_3317454 prefixEnd_3317454 1135632300787179119778875 := by
  unfold tailWord_3317454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124685965429776110110927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80664991815625472587258277 15124685965429776110110927)
  ·
    refine ⟨22687028948144664165166391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15124685965429776110110927 22687028948144664165166391)
    ·
      refine ⟨34030543422216996247749587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22687028948144664165166391 34030543422216996247749587)
      ·
        refine ⟨51045815133325494371624381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34030543422216996247749587 51045815133325494371624381)
        ·
          refine ⟨19142180674997060389359143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51045815133325494371624381 19142180674997060389359143)
          ·
            refine ⟨28713271012495590584038715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19142180674997060389359143 28713271012495590584038715)
            ·
              refine ⟨43069906518743385876058073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28713271012495590584038715 43069906518743385876058073)
              ·
                refine ⟨32302429889057539407043555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43069906518743385876058073 32302429889057539407043555)
                ·
                  refine ⟨48453644833586309110565333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32302429889057539407043555 48453644833586309110565333)
                  ·
                    refine ⟨1135632300787179119778875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48453644833586309110565333 1135632300787179119778875)
                    ·
                      rfl

theorem cell22_3317454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3317454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317454 prefixEnd_3317454 := by exact prefixLift 3317454
  have htrace : WordTrace (prefixWord ++ tailWord_3317454) baseStart_3317454 baseEnd_3317454 := by
    simpa [prefixWord, tailWord_3317454, baseEnd_3317454] using wordTrace_append hprefix tailTrace_3317454
  have hstable : (prefixWord ++ tailWord_3317454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317454).length < 2 ^ (prefixWord ++ tailWord_3317454).sum := by decide
  have hdescent : baseEnd_3317454 < baseStart_3317454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317460 : List Nat := [2, 4, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3317460 : Nat := 118140960795 + 3317460 * 2 ^ 59
def prefixEnd_3317460 : Nat := 4983230072969 + 3 ^ 40 * 3317460 * 2
def baseEnd_3317460 : Nat := 1135634354709797104128857

theorem tailTrace_3317460 : CollatzResearch.WordTrace tailWord_3317460 prefixEnd_3317460 1135634354709797104128857 := by
  unfold tailWord_3317460
  simp only [CollatzResearch.WordTrace]
  refine ⟨60498853280708235952802917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80665137707610981270403889 60498853280708235952802917)
  ·
    refine ⟨11343534990132794241150547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60498853280708235952802917 11343534990132794241150547)
    ·
      refine ⟨17015302485199191361725821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11343534990132794241150547 17015302485199191361725821)
      ·
        refine ⟨6380738431949696760647183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17015302485199191361725821 6380738431949696760647183)
        ·
          refine ⟨9571107647924545140970775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6380738431949696760647183 9571107647924545140970775)
          ·
            refine ⟨14356661471886817711456163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9571107647924545140970775 14356661471886817711456163)
            ·
              refine ⟨21534992207830226567184245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14356661471886817711456163 21534992207830226567184245)
              ·
                refine ⟨2018905519484083740673523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21534992207830226567184245 2018905519484083740673523)
                ·
                  refine ⟨3028358279226125611010285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018905519484083740673523 3028358279226125611010285)
                  ·
                    refine ⟨1135634354709797104128857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028358279226125611010285 1135634354709797104128857)
                    ·
                      rfl

theorem cell22_3317460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3317460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317460 prefixEnd_3317460 := by exact prefixLift 3317460
  have htrace : WordTrace (prefixWord ++ tailWord_3317460) baseStart_3317460 baseEnd_3317460 := by
    simpa [prefixWord, tailWord_3317460, baseEnd_3317460] using wordTrace_append hprefix tailTrace_3317460
  have hstable : (prefixWord ++ tailWord_3317460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317460).length < 2 ^ (prefixWord ++ tailWord_3317460).sum := by decide
  have hdescent : baseEnd_3317460 < baseStart_3317460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317473 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 5]
def baseStart_3317473 : Nat := 118140960795 + 3317473 * 2 ^ 59
def prefixEnd_3317473 : Nat := 4983230072969 + 3 ^ 40 * 3317473 * 2
def baseEnd_3317473 : Nat := 378546268291823134517939

theorem tailTrace_3317473 : CollatzResearch.WordTrace tailWord_3317473 prefixEnd_3317473 378546268291823134517939 := by
  unfold tailWord_3317473
  simp only [CollatzResearch.WordTrace]
  refine ⟨120998180710369375125829073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80665453806912916750552715 120998180710369375125829073)
  ·
    refine ⟨90748635532777031344371805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120998180710369375125829073 90748635532777031344371805)
    ·
      refine ⟨34030738324791386754139427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90748635532777031344371805 34030738324791386754139427)
      ·
        refine ⟨51046107487187080131209141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34030738324791386754139427 51046107487187080131209141)
        ·
          refine ⟨4785572576923788762300857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51046107487187080131209141 4785572576923788762300857)
          ·
            refine ⟨3589179432692841571725643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4785572576923788762300857 3589179432692841571725643)
            ·
              refine ⟨5383769149039262357588465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589179432692841571725643 5383769149039262357588465)
              ·
                refine ⟨4037826861779446768191349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5383769149039262357588465 4037826861779446768191349)
                ·
                  refine ⟨378546268291823134517939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4037826861779446768191349 378546268291823134517939)
                  ·
                    rfl

theorem cell22_3317473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_3317473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317473 prefixEnd_3317473 := by exact prefixLift 3317473
  have htrace : WordTrace (prefixWord ++ tailWord_3317473) baseStart_3317473 baseEnd_3317473 := by
    simpa [prefixWord, tailWord_3317473, baseEnd_3317473] using wordTrace_append hprefix tailTrace_3317473
  have hstable : (prefixWord ++ tailWord_3317473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317473).length < 2 ^ (prefixWord ++ tailWord_3317473).sum := by decide
  have hdescent : baseEnd_3317473 < baseStart_3317473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317484 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 6]
def baseStart_3317484 : Nat := 118140960795 + 3317484 * 2 ^ 59
def prefixEnd_3317484 : Nat := 4983230072969 + 3 ^ 40 * 3317484 * 2
def baseEnd_3317484 : Nat := 378547523466756347176261

theorem tailTrace_3317484 : CollatzResearch.WordTrace tailWord_3317484 prefixEnd_3317484 378547523466756347176261 := by
  unfold tailWord_3317484
  simp only [CollatzResearch.WordTrace]
  refine ⟨60499290956664762002239753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80665721275553016002986337 60499290956664762002239753)
  ·
    refine ⟨45374468217498571501679815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60499290956664762002239753 45374468217498571501679815)
    ·
      refine ⟨68061702326247857252519723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45374468217498571501679815 68061702326247857252519723)
      ·
        refine ⟨102092553489371785878779585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68061702326247857252519723 102092553489371785878779585)
        ·
          refine ⟨76569415117028839409084689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102092553489371785878779585 76569415117028839409084689)
          ·
            refine ⟨57427061337771629556813517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76569415117028839409084689 57427061337771629556813517)
            ·
              refine ⟨21535148001664361083805069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57427061337771629556813517 21535148001664361083805069)
              ·
                refine ⟨8075680500624135406426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21535148001664361083805069 8075680500624135406426901)
                ·
                  refine ⟨378547523466756347176261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8075680500624135406426901 378547523466756347176261)
                  ·
                    rfl

theorem cell22_3317484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_3317484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317484 prefixEnd_3317484 := by exact prefixLift 3317484
  have htrace : WordTrace (prefixWord ++ tailWord_3317484) baseStart_3317484 baseEnd_3317484 := by
    simpa [prefixWord, tailWord_3317484, baseEnd_3317484] using wordTrace_append hprefix tailTrace_3317484
  have hstable : (prefixWord ++ tailWord_3317484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317484).length < 2 ^ (prefixWord ++ tailWord_3317484).sum := by decide
  have hdescent : baseEnd_3317484 < baseStart_3317484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317499 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 1, 5]
def baseStart_3317499 : Nat := 118140960795 + 3317499 * 2 ^ 59
def prefixEnd_3317499 : Nat := 4983230072969 + 3 ^ 40 * 3317499 * 2
def baseEnd_3317499 : Nat := 1135647705206814002403737

theorem tailTrace_3317499 : CollatzResearch.WordTrace tailWord_3317499 prefixEnd_3317499 1135647705206814002403737 := by
  unfold tailWord_3317499
  simp only [CollatzResearch.WordTrace]
  refine ⟨120999129008275181566275551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80666086005516787710850367 120999129008275181566275551)
  ·
    refine ⟨181498693512412772349413327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120999129008275181566275551 181498693512412772349413327)
    ·
      refine ⟨272248040268619158524119991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181498693512412772349413327 272248040268619158524119991)
      ·
        refine ⟨408372060402928737786179987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272248040268619158524119991 408372060402928737786179987)
        ·
          refine ⟨612558090604393106679269981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408372060402928737786179987 612558090604393106679269981)
          ·
            refine ⟨229709283976647415004726243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612558090604393106679269981 229709283976647415004726243)
            ·
              refine ⟨344563925964971122507089365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229709283976647415004726243 344563925964971122507089365)
              ·
                refine ⟨8075717014804010683759907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 344563925964971122507089365 8075717014804010683759907)
                ·
                  refine ⟨12113575522206016025639861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075717014804010683759907 12113575522206016025639861)
                  ·
                    refine ⟨1135647705206814002403737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12113575522206016025639861 1135647705206814002403737)
                    ·
                      rfl

theorem cell22_3317499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_3317499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317499 prefixEnd_3317499 := by exact prefixLift 3317499
  have htrace : WordTrace (prefixWord ++ tailWord_3317499) baseStart_3317499 baseEnd_3317499 := by
    simpa [prefixWord, tailWord_3317499, baseEnd_3317499] using wordTrace_append hprefix tailTrace_3317499
  have hstable : (prefixWord ++ tailWord_3317499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317499).length < 2 ^ (prefixWord ++ tailWord_3317499).sum := by decide
  have hdescent : baseEnd_3317499 < baseStart_3317499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317516 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_3317516 : Nat := 118140960795 + 3317516 * 2 ^ 59
def prefixEnd_3317516 : Nat := 4983230072969 + 3 ^ 40 * 3317516 * 2
def baseEnd_3317516 : Nat := 1135653524654231624728685

theorem tailTrace_3317516 : CollatzResearch.WordTrace tailWord_3317516 prefixEnd_3317516 1135653524654231624728685 := by
  unfold tailWord_3317516
  simp only [CollatzResearch.WordTrace]
  refine ⟨60499874524606796734822201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80666499366142395646429601 60499874524606796734822201)
  ·
    refine ⟨45374905893455097551116651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60499874524606796734822201 45374905893455097551116651)
    ·
      refine ⟨68062358840182646326674977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45374905893455097551116651 68062358840182646326674977)
      ·
        refine ⟨51046769130136984745006233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68062358840182646326674977 51046769130136984745006233)
        ·
          refine ⟨38285076847602738558754675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51046769130136984745006233 38285076847602738558754675)
          ·
            refine ⟨57427615271404107838132013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38285076847602738558754675 57427615271404107838132013)
            ·
              refine ⟨21535355726776540439299505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57427615271404107838132013 21535355726776540439299505)
              ·
                refine ⟨16151516795082405329474629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21535355726776540439299505 16151516795082405329474629)
                ·
                  refine ⟨3028409399077950999276493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16151516795082405329474629 3028409399077950999276493)
                  ·
                    refine ⟨1135653524654231624728685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028409399077950999276493 1135653524654231624728685)
                    ·
                      rfl

theorem cell22_3317516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_3317516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317516 prefixEnd_3317516 := by exact prefixLift 3317516
  have htrace : WordTrace (prefixWord ++ tailWord_3317516) baseStart_3317516 baseEnd_3317516 := by
    simpa [prefixWord, tailWord_3317516, baseEnd_3317516] using wordTrace_append hprefix tailTrace_3317516
  have hstable : (prefixWord ++ tailWord_3317516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317516).length < 2 ^ (prefixWord ++ tailWord_3317516).sum := by decide
  have hdescent : baseEnd_3317516 < baseStart_3317516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317518 : List Nat := [4, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_3317518 : Nat := 118140960795 + 3317518 * 2 ^ 59
def prefixEnd_3317518 : Nat := 4983230072969 + 3 ^ 40 * 3317518 * 2
def baseEnd_3317518 : Nat := 378551403098368095392893

theorem tailTrace_3317518 : CollatzResearch.WordTrace tailWord_3317518 prefixEnd_3317518 378551403098368095392893 := by
  unfold tailWord_3317518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124977749400793476402151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80666547996804231874144805 15124977749400793476402151)
  ·
    refine ⟨22687466624101190214603227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15124977749400793476402151 22687466624101190214603227)
    ·
      refine ⟨34031199936151785321904841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22687466624101190214603227 34031199936151785321904841)
      ·
        refine ⟨25523399952113838991428631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34031199936151785321904841 25523399952113838991428631)
        ·
          refine ⟨38285099928170758487142947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25523399952113838991428631 38285099928170758487142947)
          ·
            refine ⟨57427649892256137730714421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38285099928170758487142947 57427649892256137730714421)
            ·
              refine ⟨5383842177399012912254477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57427649892256137730714421 5383842177399012912254477)
              ·
                refine ⟨2018940816524629842095429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5383842177399012912254477 2018940816524629842095429)
                ·
                  refine ⟨378551403098368095392893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018940816524629842095429 378551403098368095392893)
                  ·
                    rfl

theorem cell22_3317518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_3317518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317518 prefixEnd_3317518 := by exact prefixLift 3317518
  have htrace : WordTrace (prefixWord ++ tailWord_3317518) baseStart_3317518 baseEnd_3317518 := by
    simpa [prefixWord, tailWord_3317518, baseEnd_3317518] using wordTrace_append hprefix tailTrace_3317518
  have hstable : (prefixWord ++ tailWord_3317518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317518).length < 2 ^ (prefixWord ++ tailWord_3317518).sum := by decide
  have hdescent : baseEnd_3317518 < baseStart_3317518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317559 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3317559 : Nat := 118140960795 + 3317559 * 2 ^ 59
def prefixEnd_3317559 : Nat := 4983230072969 + 3 ^ 40 * 3317559 * 2
def baseEnd_3317559 : Nat := 1135668244432993845903553

theorem tailTrace_3317559 : CollatzResearch.WordTrace tailWord_3317559 prefixEnd_3317559 1135668244432993845903553 := by
  unfold tailWord_3317559
  simp only [CollatzResearch.WordTrace]
  refine ⟨121001317388057811813459731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80667544925371874542306487 121001317388057811813459731)
  ·
    refine ⟨181501976082086717720189597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121001317388057811813459731 181501976082086717720189597)
    ·
      refine ⟨68063241030782519145071099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181501976082086717720189597 68063241030782519145071099)
      ·
        refine ⟨102094861546173778717606649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68063241030782519145071099 102094861546173778717606649)
        ·
          refine ⟨76571146159630334038204987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102094861546173778717606649 76571146159630334038204987)
          ·
            refine ⟨114856719239445501057307481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76571146159630334038204987 114856719239445501057307481)
            ·
              refine ⟨86142539429584125792980611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114856719239445501057307481 86142539429584125792980611)
              ·
                refine ⟨129213809144376188689470917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86142539429584125792980611 129213809144376188689470917)
                ·
                  refine ⟨24227589214570535379275797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129213809144376188689470917 24227589214570535379275797)
                  ·
                    refine ⟨1135668244432993845903553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24227589214570535379275797 1135668244432993845903553)
                    ·
                      rfl

theorem cell22_3317559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3317559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317559 prefixEnd_3317559 := by exact prefixLift 3317559
  have htrace : WordTrace (prefixWord ++ tailWord_3317559) baseStart_3317559 baseEnd_3317559 := by
    simpa [prefixWord, tailWord_3317559, baseEnd_3317559] using wordTrace_append hprefix tailTrace_3317559
  have hstable : (prefixWord ++ tailWord_3317559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317559).length < 2 ^ (prefixWord ++ tailWord_3317559).sum := by decide
  have hdescent : baseEnd_3317559 < baseStart_3317559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317642 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_3317642 : Nat := 118140960795 + 3317642 * 2 ^ 59
def prefixEnd_3317642 : Nat := 4983230072969 + 3 ^ 40 * 3317642 * 2
def baseEnd_3317642 : Nat := 378565552343069765359433

theorem tailTrace_3317642 : CollatzResearch.WordTrace tailWord_3317642 prefixEnd_3317642 378565552343069765359433 := by
  unfold tailWord_3317642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30251086161689279247182795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80669563097838077992487453 30251086161689279247182795)
  ·
    refine ⟨45376629242533918870774193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30251086161689279247182795 45376629242533918870774193)
    ·
      refine ⟨34032471931900439153080645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45376629242533918870774193 34032471931900439153080645)
      ·
        refine ⟨6381088487231332341202621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34032471931900439153080645 6381088487231332341202621)
        ·
          refine ⟨2392908182711749627950983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6381088487231332341202621 2392908182711749627950983)
          ·
            refine ⟨3589362274067624441926475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392908182711749627950983 3589362274067624441926475)
            ·
              refine ⟨5384043411101436662889713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589362274067624441926475 5384043411101436662889713)
              ·
                refine ⟨4038032558326077497167285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384043411101436662889713 4038032558326077497167285)
                ·
                  refine ⟨378565552343069765359433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038032558326077497167285 378565552343069765359433)
                  ·
                    rfl

theorem cell22_3317642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_3317642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317642 prefixEnd_3317642 := by exact prefixLift 3317642
  have htrace : WordTrace (prefixWord ++ tailWord_3317642) baseStart_3317642 baseEnd_3317642 := by
    simpa [prefixWord, tailWord_3317642, baseEnd_3317642] using wordTrace_append hprefix tailTrace_3317642
  have hstable : (prefixWord ++ tailWord_3317642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317642).length < 2 ^ (prefixWord ++ tailWord_3317642).sum := by decide
  have hdescent : baseEnd_3317642 < baseStart_3317642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317653 : List Nat := [1, 3, 2, 1, 1, 3, 1, 6, 4]
def baseStart_3317653 : Nat := 118140960795 + 3317653 * 2 ^ 59
def prefixEnd_3317653 : Nat := 4983230072969 + 3 ^ 40 * 3317653 * 2
def baseEnd_3317653 : Nat := 378566807518002978017755

theorem tailTrace_3317653 : CollatzResearch.WordTrace tailWord_3317653 prefixEnd_3317653 378566807518002978017755 := by
  unfold tailWord_3317653
  simp only [CollatzResearch.WordTrace]
  refine ⟨121004745849717265867381613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80669830566478177244921075 121004745849717265867381613)
  ·
    refine ⟨45376779693643974700268105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121004745849717265867381613 45376779693643974700268105)
    ·
      refine ⟨34032584770232981025201079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45376779693643974700268105 34032584770232981025201079)
      ·
        refine ⟨51048877155349471537801619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34032584770232981025201079 51048877155349471537801619)
        ·
          refine ⟨76573315733024207306702429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51048877155349471537801619 76573315733024207306702429)
          ·
            refine ⟨28714993399884077740013411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76573315733024207306702429 28714993399884077740013411)
            ·
              refine ⟨43072490099826116610020117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28714993399884077740013411 43072490099826116610020117)
              ·
                refine ⟨2019022973429349216094693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43072490099826116610020117 2019022973429349216094693)
                ·
                  refine ⟨378566807518002978017755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019022973429349216094693 378566807518002978017755)
                  ·
                    rfl

theorem cell22_3317653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_3317653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317653 prefixEnd_3317653 := by exact prefixLift 3317653
  have htrace : WordTrace (prefixWord ++ tailWord_3317653) baseStart_3317653 baseEnd_3317653 := by
    simpa [prefixWord, tailWord_3317653, baseEnd_3317653] using wordTrace_append hprefix tailTrace_3317653
  have hstable : (prefixWord ++ tailWord_3317653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317653).length < 2 ^ (prefixWord ++ tailWord_3317653).sum := by decide
  have hdescent : baseEnd_3317653 < baseStart_3317653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317668 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_3317668 : Nat := 118140960795 + 3317668 * 2 ^ 59
def prefixEnd_3317668 : Nat := 4983230072969 + 3 ^ 40 * 3317668 * 2
def baseEnd_3317668 : Nat := 1135705557360553894928219

theorem tailTrace_3317668 : CollatzResearch.WordTrace tailWord_3317668 prefixEnd_3317668 1135705557360553894928219 := by
  unfold tailWord_3317668
  simp only [CollatzResearch.WordTrace]
  refine ⟨60502646472331461714588829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80670195296441948952785105 60502646472331461714588829)
  ·
    refine ⟨22688492427124298142970811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60502646472331461714588829 22688492427124298142970811)
    ·
      refine ⟨34032738640686447214456217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22688492427124298142970811 34032738640686447214456217)
      ·
        refine ⟨25524553980514835410842163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34032738640686447214456217 25524553980514835410842163)
        ·
          refine ⟨38286830970772253116263245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25524553980514835410842163 38286830970772253116263245)
          ·
            refine ⟨14357561614039594918598717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38286830970772253116263245 14357561614039594918598717)
            ·
              refine ⟨5384085605264848094474519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14357561614039594918598717 5384085605264848094474519)
              ·
                refine ⟨8076128407897272141711779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384085605264848094474519 8076128407897272141711779)
                ·
                  refine ⟨12114192611845908212567669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8076128407897272141711779 12114192611845908212567669)
                  ·
                    refine ⟨1135705557360553894928219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12114192611845908212567669 1135705557360553894928219)
                    ·
                      rfl

theorem cell22_3317668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_3317668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317668 prefixEnd_3317668 := by exact prefixLift 3317668
  have htrace : WordTrace (prefixWord ++ tailWord_3317668) baseStart_3317668 baseEnd_3317668 := by
    simpa [prefixWord, tailWord_3317668, baseEnd_3317668] using wordTrace_append hprefix tailTrace_3317668
  have hstable : (prefixWord ++ tailWord_3317668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317668).length < 2 ^ (prefixWord ++ tailWord_3317668).sum := by decide
  have hdescent : baseEnd_3317668 < baseStart_3317668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317711 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 2, 6]
def baseStart_3317711 : Nat := 118140960795 + 3317711 * 2 ^ 59
def prefixEnd_3317711 : Nat := 4983230072969 + 3 ^ 40 * 3317711 * 2
def baseEnd_3317711 : Nat := 1135720277139316116103087

theorem tailTrace_3317711 : CollatzResearch.WordTrace tailWord_3317711 prefixEnd_3317711 1135720277139316116103087 := by
  unfold tailWord_3317711
  simp only [CollatzResearch.WordTrace]
  refine ⟨121006861283507141772992987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80671240855671427848661991 121006861283507141772992987)
  ·
    refine ⟨181510291925260712659489481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121006861283507141772992987 181510291925260712659489481)
    ·
      refine ⟨136132718943945534494617111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181510291925260712659489481 136132718943945534494617111)
      ·
        refine ⟨204199078415918301741925667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136132718943945534494617111 204199078415918301741925667)
        ·
          refine ⟨306298617623877452612888501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204199078415918301741925667 306298617623877452612888501)
          ·
            refine ⟨28715495402238511182458297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 306298617623877452612888501 28715495402238511182458297)
            ·
              refine ⟨21536621551678883386843723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28715495402238511182458297 21536621551678883386843723)
              ·
                refine ⟨32304932327518325080265585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21536621551678883386843723 32304932327518325080265585)
                ·
                  refine ⟨24228699245638743810199189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32304932327518325080265585 24228699245638743810199189)
                  ·
                    refine ⟨1135720277139316116103087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24228699245638743810199189 1135720277139316116103087)
                    ·
                      rfl

theorem cell22_3317711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_3317711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317711 prefixEnd_3317711 := by exact prefixLift 3317711
  have htrace : WordTrace (prefixWord ++ tailWord_3317711) baseStart_3317711 baseEnd_3317711 := by
    simpa [prefixWord, tailWord_3317711, baseEnd_3317711] using wordTrace_append hprefix tailTrace_3317711
  have hstable : (prefixWord ++ tailWord_3317711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317711).length < 2 ^ (prefixWord ++ tailWord_3317711).sum := by decide
  have hdescent : baseEnd_3317711 < baseStart_3317711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317713 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 3, 3]
def baseStart_3317713 : Nat := 118140960795 + 3317713 * 2 ^ 59
def prefixEnd_3317713 : Nat := 4983230072969 + 3 ^ 40 * 3317713 * 2
def baseEnd_3317713 : Nat := 1135720961780188777553081

theorem tailTrace_3317713 : CollatzResearch.WordTrace tailWord_3317713 prefixEnd_3317713 1135720961780188777553081 := by
  unfold tailWord_3317713
  simp only [CollatzResearch.WordTrace]
  refine ⟨121006934229499896114565793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80671289486333264076377195 121006934229499896114565793)
  ·
    refine ⟨90755200672124922085924345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121006934229499896114565793 90755200672124922085924345)
    ·
      refine ⟨68066400504093691564443259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90755200672124922085924345 68066400504093691564443259)
      ·
        refine ⟨102099600756140537346664889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68066400504093691564443259 102099600756140537346664889)
        ·
          refine ⟨76574700567105403009998667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102099600756140537346664889 76574700567105403009998667)
          ·
            refine ⟨114862050850658104514998001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76574700567105403009998667 114862050850658104514998001)
            ·
              refine ⟨86146538137993578386248501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114862050850658104514998001 86146538137993578386248501)
              ·
                refine ⟨8076237950436897973710797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86146538137993578386248501 8076237950436897973710797)
                ·
                  refine ⟨3028589231413836740141549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8076237950436897973710797 3028589231413836740141549)
                  ·
                    refine ⟨1135720961780188777553081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028589231413836740141549 1135720961780188777553081)
                    ·
                      rfl

theorem cell22_3317713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_3317713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317713 prefixEnd_3317713 := by exact prefixLift 3317713
  have htrace : WordTrace (prefixWord ++ tailWord_3317713) baseStart_3317713 baseEnd_3317713 := by
    simpa [prefixWord, tailWord_3317713, baseEnd_3317713] using wordTrace_append hprefix tailTrace_3317713
  have hstable : (prefixWord ++ tailWord_3317713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317713).length < 2 ^ (prefixWord ++ tailWord_3317713).sum := by decide
  have hdescent : baseEnd_3317713 < baseStart_3317713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317766 : List Nat := [6, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3317766 : Nat := 118140960795 + 3317766 * 2 ^ 59
def prefixEnd_3317766 : Nat := 4983230072969 + 3 ^ 40 * 3317766 * 2
def baseEnd_3317766 : Nat := 126193233862590478441991

theorem tailTrace_3317766 : CollatzResearch.WordTrace tailWord_3317766 prefixEnd_3317766 126193233862590478441991 := by
  unfold tailWord_3317766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781527103072121442695161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80672578198871924110830101 3781527103072121442695161)
  ·
    refine ⟨2836145327304091082021371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3781527103072121442695161 2836145327304091082021371)
    ·
      refine ⟨4254217990956136623032057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836145327304091082021371 4254217990956136623032057)
      ·
        refine ⟨3190663493217102467274043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4254217990956136623032057 3190663493217102467274043)
        ·
          refine ⟨4785995239825653700911065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3190663493217102467274043 4785995239825653700911065)
          ·
            refine ⟨3589496429869240275683299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4785995239825653700911065 3589496429869240275683299)
            ·
              refine ⟨5384244644803860413524949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589496429869240275683299 5384244644803860413524949)
              ·
                refine ⟨126193233862590478441991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5384244644803860413524949 126193233862590478441991)
                ·
                  rfl

theorem cell22_3317766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3317766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317766 prefixEnd_3317766 := by exact prefixLift 3317766
  have htrace : WordTrace (prefixWord ++ tailWord_3317766) baseStart_3317766 baseEnd_3317766 := by
    simpa [prefixWord, tailWord_3317766, baseEnd_3317766] using wordTrace_append hprefix tailTrace_3317766
  have hstable : (prefixWord ++ tailWord_3317766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317766).length < 2 ^ (prefixWord ++ tailWord_3317766).sum := by decide
  have hdescent : baseEnd_3317766 < baseStart_3317766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317788 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 8]
def baseStart_3317788 : Nat := 118140960795 + 3317788 * 2 ^ 59
def prefixEnd_3317788 : Nat := 4983230072969 + 3 ^ 40 * 3317788 * 2
def baseEnd_3317788 : Nat := 378582211937637860642617

theorem tailTrace_3317788 : CollatzResearch.WordTrace tailWord_3317788 prefixEnd_3317788 378582211937637860642617 := by
  unfold tailWord_3317788
  simp only [CollatzResearch.WordTrace]
  refine ⟨60504834852114091961773009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80673113136152122615697345 60504834852114091961773009)
  ·
    refine ⟨45378626139085568971329757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60504834852114091961773009 45378626139085568971329757)
    ·
      refine ⟨17016984802157088364248659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45378626139085568971329757 17016984802157088364248659)
      ·
        refine ⟨25525477203235632546372989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17016984802157088364248659 25525477203235632546372989)
        ·
          refine ⟨9572053951213362204889871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25525477203235632546372989 9572053951213362204889871)
          ·
            refine ⟨14358080926820043307334807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572053951213362204889871 14358080926820043307334807)
            ·
              refine ⟨21537121390230064961002211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14358080926820043307334807 21537121390230064961002211)
              ·
                refine ⟨32305682085345097441503317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21537121390230064961002211 32305682085345097441503317)
                ·
                  refine ⟨378582211937637860642617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32305682085345097441503317 378582211937637860642617)
                  ·
                    rfl

theorem cell22_3317788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_3317788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317788 prefixEnd_3317788 := by exact prefixLift 3317788
  have htrace : WordTrace (prefixWord ++ tailWord_3317788) baseStart_3317788 baseEnd_3317788 := by
    simpa [prefixWord, tailWord_3317788, baseEnd_3317788] using wordTrace_append hprefix tailTrace_3317788
  have hstable : (prefixWord ++ tailWord_3317788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317788).length < 2 ^ (prefixWord ++ tailWord_3317788).sum := by decide
  have hdescent : baseEnd_3317788 < baseStart_3317788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317818 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_3317818 : Nat := 118140960795 + 3317818 * 2 ^ 59
def prefixEnd_3317818 : Nat := 4983230072969 + 3 ^ 40 * 3317818 * 2
def baseEnd_3317818 : Nat := 1135756905426003503677759

theorem tailTrace_3317818 : CollatzResearch.WordTrace tailWord_3317818 prefixEnd_3317818 1135756905426003503677759 := by
  unfold tailWord_3317818
  simp only [CollatzResearch.WordTrace]
  refine ⟨30252690973529874761784527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80673842596079666031425405 30252690973529874761784527)
  ·
    refine ⟨45379036460294812142676791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30252690973529874761784527 45379036460294812142676791)
    ·
      refine ⟨68068554690442218214015187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45379036460294812142676791 68068554690442218214015187)
      ·
        refine ⟨102102832035663327321022781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68068554690442218214015187 102102832035663327321022781)
        ·
          refine ⟨38288562013373747745383543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102102832035663327321022781 38288562013373747745383543)
          ·
            refine ⟨57432843020060621618075315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38288562013373747745383543 57432843020060621618075315)
            ·
              refine ⟨86149264530090932427112973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57432843020060621618075315 86149264530090932427112973)
              ·
                refine ⟨32305974198784099660167365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86149264530090932427112973 32305974198784099660167365)
                ·
                  refine ⟨6057370162272018686281381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32305974198784099660167365 6057370162272018686281381)
                  ·
                    refine ⟨1135756905426003503677759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6057370162272018686281381 1135756905426003503677759)
                    ·
                      rfl

theorem cell22_3317818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_3317818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317818 prefixEnd_3317818 := by exact prefixLift 3317818
  have htrace : WordTrace (prefixWord ++ tailWord_3317818) baseStart_3317818 baseEnd_3317818 := by
    simpa [prefixWord, tailWord_3317818, baseEnd_3317818] using wordTrace_append hprefix tailTrace_3317818
  have hstable : (prefixWord ++ tailWord_3317818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317818).length < 2 ^ (prefixWord ++ tailWord_3317818).sum := by decide
  have hdescent : baseEnd_3317818 < baseStart_3317818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317820 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_3317820 : Nat := 118140960795 + 3317820 * 2 ^ 59
def prefixEnd_3317820 : Nat := 4983230072969 + 3 ^ 40 * 3317820 * 2
def baseEnd_3317820 : Nat := 1135757590066876165127753

theorem tailTrace_3317820 : CollatzResearch.WordTrace tailWord_3317820 prefixEnd_3317820 1135757590066876165127753 := by
  unfold tailWord_3317820
  simp only [CollatzResearch.WordTrace]
  refine ⟨60505418420056126694355457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80673891226741502259140609 60505418420056126694355457)
  ·
    refine ⟨45379063815042095020766593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60505418420056126694355457 45379063815042095020766593)
    ·
      refine ⟨34034297861281571265574945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45379063815042095020766593 34034297861281571265574945)
      ·
        refine ⟨25525723395961178449181209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34034297861281571265574945 25525723395961178449181209)
        ·
          refine ⟨19144292546970883836885907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25525723395961178449181209 19144292546970883836885907)
          ·
            refine ⟨28716438820456325755328861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19144292546970883836885907 28716438820456325755328861)
            ·
              refine ⟨10768664557671122158248323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28716438820456325755328861 10768664557671122158248323)
              ·
                refine ⟨16152996836506683237372485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10768664557671122158248323 16152996836506683237372485)
                ·
                  refine ⟨3028686906845003107007341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16152996836506683237372485 3028686906845003107007341)
                  ·
                    refine ⟨1135757590066876165127753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028686906845003107007341 1135757590066876165127753)
                    ·
                      rfl

theorem cell22_3317820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_3317820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317820 prefixEnd_3317820 := by exact prefixLift 3317820
  have htrace : WordTrace (prefixWord ++ tailWord_3317820) baseStart_3317820 baseEnd_3317820 := by
    simpa [prefixWord, tailWord_3317820, baseEnd_3317820] using wordTrace_append hprefix tailTrace_3317820
  have hstable : (prefixWord ++ tailWord_3317820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317820).length < 2 ^ (prefixWord ++ tailWord_3317820).sum := by decide
  have hdescent : baseEnd_3317820 < baseStart_3317820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317822 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_3317822 : Nat := 118140960795 + 3317822 * 2 ^ 59
def prefixEnd_3317822 : Nat := 4983230072969 + 3 ^ 40 * 3317822 * 2
def baseEnd_3317822 : Nat := 378586091569249608859249

theorem tailTrace_3317822 : CollatzResearch.WordTrace tailWord_3317822 prefixEnd_3317822 378586091569249608859249 := by
  unfold tailWord_3317822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126363723263125966285465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80673939857403338486855813 15126363723263125966285465)
  ·
    refine ⟨11344772792447344474714099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15126363723263125966285465 11344772792447344474714099)
    ·
      refine ⟨17017159188671016712071149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11344772792447344474714099 17017159188671016712071149)
      ·
        refine ⟨6381434695751631267026681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17017159188671016712071149 6381434695751631267026681)
        ·
          refine ⟨4786076021813723450270011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6381434695751631267026681 4786076021813723450270011)
          ·
            refine ⟨7179114032720585175405017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786076021813723450270011 7179114032720585175405017)
            ·
              refine ⟨5384335524540438881553763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7179114032720585175405017 5384335524540438881553763)
              ·
                refine ⟨8076503286810658322330645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384335524540438881553763 8076503286810658322330645)
                ·
                  refine ⟨378586091569249608859249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8076503286810658322330645 378586091569249608859249)
                  ·
                    rfl

theorem cell22_3317822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_3317822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317822 prefixEnd_3317822 := by exact prefixLift 3317822
  have htrace : WordTrace (prefixWord ++ tailWord_3317822) baseStart_3317822 baseEnd_3317822 := by
    simpa [prefixWord, tailWord_3317822, baseEnd_3317822] using wordTrace_append hprefix tailTrace_3317822
  have hstable : (prefixWord ++ tailWord_3317822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317822).length < 2 ^ (prefixWord ++ tailWord_3317822).sum := by decide
  have hdescent : baseEnd_3317822 < baseStart_3317822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317933 : List Nat := [1, 5, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3317933 : Nat := 118140960795 + 3317933 * 2 ^ 59
def prefixEnd_3317933 : Nat := 4983230072969 + 3 ^ 40 * 3317933 * 2
def baseEnd_3317933 : Nat := 1135796272276181537052407

theorem tailTrace_3317933 : CollatzResearch.WordTrace tailWord_3317933 prefixEnd_3317933 1135796272276181537052407 := by
  unfold tailWord_3317933
  simp only [CollatzResearch.WordTrace]
  refine ⟨121014958288702873687574453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80676638859135249125049635 121014958288702873687574453)
  ·
    refine ⟨11345152339565894408210105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121014958288702873687574453 11345152339565894408210105)
    ·
      refine ⟨8508864254674420806157579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11345152339565894408210105 8508864254674420806157579)
      ·
        refine ⟨12763296382011631209236369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508864254674420806157579 12763296382011631209236369)
        ·
          refine ⟨9572472286508723406927277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12763296382011631209236369 9572472286508723406927277)
          ·
            refine ⟨3589677107440771277597729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9572472286508723406927277 3589677107440771277597729)
            ·
              refine ⟨2692257830580578458198297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589677107440771277597729 2692257830580578458198297)
              ·
                refine ⟨2019193372935433843648723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692257830580578458198297 2019193372935433843648723)
                ·
                  refine ⟨3028790059403150765473085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019193372935433843648723 3028790059403150765473085)
                  ·
                    refine ⟨1135796272276181537052407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028790059403150765473085 1135796272276181537052407)
                    ·
                      rfl

theorem cell22_3317933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3317933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317933 prefixEnd_3317933 := by exact prefixLift 3317933
  have htrace : WordTrace (prefixWord ++ tailWord_3317933) baseStart_3317933 baseEnd_3317933 := by
    simpa [prefixWord, tailWord_3317933, baseEnd_3317933] using wordTrace_append hprefix tailTrace_3317933
  have hstable : (prefixWord ++ tailWord_3317933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317933).length < 2 ^ (prefixWord ++ tailWord_3317933).sum := by decide
  have hdescent : baseEnd_3317933 < baseStart_3317933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317989 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_3317989 : Nat := 118140960795 + 3317989 * 2 ^ 59
def prefixEnd_3317989 : Nat := 4983230072969 + 3 ^ 40 * 3317989 * 2
def baseEnd_3317989 : Nat := 1135815442220616057652235

theorem tailTrace_3317989 : CollatzResearch.WordTrace tailWord_3317989 prefixEnd_3317989 1135815442220616057652235 := by
  unfold tailWord_3317989
  simp only [CollatzResearch.WordTrace]
  refine ⟨121017000776499995251613021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80678000517666663501075347 121017000776499995251613021)
  ·
    refine ⟨45381375291187498219354883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121017000776499995251613021 45381375291187498219354883)
    ·
      refine ⟨68072062936781247329032325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45381375291187498219354883 68072062936781247329032325)
      ·
        refine ⟨12763511800646483874193561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68072062936781247329032325 12763511800646483874193561)
        ·
          refine ⟨9572633850484862905645171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12763511800646483874193561 9572633850484862905645171)
          ·
            refine ⟨14358950775727294358467757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572633850484862905645171 14358950775727294358467757)
            ·
              refine ⟨5384606540897735384425409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14358950775727294358467757 5384606540897735384425409)
              ·
                refine ⟨4038454905673301538319057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384606540897735384425409 4038454905673301538319057)
                ·
                  refine ⟨3028841179254976153739293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038454905673301538319057 3028841179254976153739293)
                  ·
                    refine ⟨1135815442220616057652235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028841179254976153739293 1135815442220616057652235)
                    ·
                      rfl

theorem cell22_3317989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_3317989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317989 prefixEnd_3317989 := by exact prefixLift 3317989
  have htrace : WordTrace (prefixWord ++ tailWord_3317989) baseStart_3317989 baseEnd_3317989 := by
    simpa [prefixWord, tailWord_3317989, baseEnd_3317989] using wordTrace_append hprefix tailTrace_3317989
  have hstable : (prefixWord ++ tailWord_3317989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317989).length < 2 ^ (prefixWord ++ tailWord_3317989).sum := by decide
  have hdescent : baseEnd_3317989 < baseStart_3317989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318017 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3318017 : Nat := 118140960795 + 3318017 * 2 ^ 59
def prefixEnd_3318017 : Nat := 4983230072969 + 3 ^ 40 * 3318017 * 2
def baseEnd_3318017 : Nat := 1135825027192833317952149

theorem tailTrace_3318017 : CollatzResearch.WordTrace tailWord_3318017 prefixEnd_3318017 1135825027192833317952149 := by
  unfold tailWord_3318017
  simp only [CollatzResearch.WordTrace]
  refine ⟨121018022020398556033632305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80678681346932370689088203 121018022020398556033632305)
  ·
    refine ⟨90763516515298917025224229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121018022020398556033632305 90763516515298917025224229)
    ·
      refine ⟨17018159346618546942229543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90763516515298917025224229 17018159346618546942229543)
      ·
        refine ⟨25527239019927820413344315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17018159346618546942229543 25527239019927820413344315)
        ·
          refine ⟨38290858529891730620016473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25527239019927820413344315 38290858529891730620016473)
          ·
            refine ⟨28718143897418797965012355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38290858529891730620016473 28718143897418797965012355)
            ·
              refine ⟨43077215846128196947518533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28718143897418797965012355 43077215846128196947518533)
              ·
                refine ⟨8076977971149036927659725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43077215846128196947518533 8076977971149036927659725)
                ·
                  refine ⟨3028866739180888847872397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8076977971149036927659725 3028866739180888847872397)
                  ·
                    refine ⟨1135825027192833317952149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028866739180888847872397 1135825027192833317952149)
                    ·
                      rfl

theorem cell22_3318017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3318017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318017 prefixEnd_3318017 := by exact prefixLift 3318017
  have htrace : WordTrace (prefixWord ++ tailWord_3318017) baseStart_3318017 baseEnd_3318017 := by
    simpa [prefixWord, tailWord_3318017, baseEnd_3318017] using wordTrace_append hprefix tailTrace_3318017
  have hstable : (prefixWord ++ tailWord_3318017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318017).length < 2 ^ (prefixWord ++ tailWord_3318017).sum := by decide
  have hdescent : baseEnd_3318017 < baseStart_3318017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318030 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_3318030 : Nat := 118140960795 + 3318030 * 2 ^ 59
def prefixEnd_3318030 : Nat := 4983230072969 + 3 ^ 40 * 3318030 * 2
def baseEnd_3318030 : Nat := 378609825786168539125703

theorem tailTrace_3318030 : CollatzResearch.WordTrace tailWord_3318030 prefixEnd_3318030 378609825786168539125703 := by
  unfold tailWord_3318030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127312021168932406731943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80678997446234306169237029 15127312021168932406731943)
  ·
    refine ⟨22690968031753398610097915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15127312021168932406731943 22690968031753398610097915)
    ·
      refine ⟨34036452047630097915146873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22690968031753398610097915 34036452047630097915146873)
      ·
        refine ⟨25527339035722573436360155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34036452047630097915146873 25527339035722573436360155)
        ·
          refine ⟨38291008553583860154540233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25527339035722573436360155 38291008553583860154540233)
          ·
            refine ⟨28718256415187895115905175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38291008553583860154540233 28718256415187895115905175)
            ·
              refine ⟨43077384622781842673857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28718256415187895115905175 43077384622781842673857763)
              ·
                refine ⟨64616076934172764010786645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43077384622781842673857763 64616076934172764010786645)
                ·
                  refine ⟨378609825786168539125703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64616076934172764010786645 378609825786168539125703)
                  ·
                    rfl

theorem cell22_3318030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_3318030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318030 prefixEnd_3318030 := by exact prefixLift 3318030
  have htrace : WordTrace (prefixWord ++ tailWord_3318030) baseStart_3318030 baseEnd_3318030 := by
    simpa [prefixWord, tailWord_3318030, baseEnd_3318030] using wordTrace_append hprefix tailTrace_3318030
  have hstable : (prefixWord ++ tailWord_3318030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318030).length < 2 ^ (prefixWord ++ tailWord_3318030).sum := by decide
  have hdescent : baseEnd_3318030 < baseStart_3318030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318051 : List Nat := [1, 1, 1, 4, 2, 2, 5, 2, 1, 3]
def baseStart_3318051 : Nat := 118140960795 + 3318051 * 2 ^ 59
def prefixEnd_3318051 : Nat := 4983230072969 + 3 ^ 40 * 3318051 * 2
def baseEnd_3318051 : Nat := 1135836666087668562602045

theorem tailTrace_3318051 : CollatzResearch.WordTrace tailWord_3318051 prefixEnd_3318051 1135836666087668562602045 := by
  unfold tailWord_3318051
  simp only [CollatzResearch.WordTrace]
  refine ⟨121019262102275379840370007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80679508068183586560246671 121019262102275379840370007)
  ·
    refine ⟨181528893153413069760555011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121019262102275379840370007 181528893153413069760555011)
    ·
      refine ⟨272293339730119604640832517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181528893153413069760555011 272293339730119604640832517)
      ·
        refine ⟨51055001199397425870156097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272293339730119604640832517 51055001199397425870156097)
        ·
          refine ⟨38291250899548069402617073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51055001199397425870156097 38291250899548069402617073)
          ·
            refine ⟨28718438174661052051962805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38291250899548069402617073 28718438174661052051962805)
            ·
              refine ⟨2692353578874473629871513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28718438174661052051962805 2692353578874473629871513)
              ·
                refine ⟨2019265184155855222403635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692353578874473629871513 2019265184155855222403635)
                ·
                  refine ⟨3028897776233782833605453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019265184155855222403635 3028897776233782833605453)
                  ·
                    refine ⟨1135836666087668562602045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028897776233782833605453 1135836666087668562602045)
                    ·
                      rfl

theorem cell22_3318051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 3].length) (baseStart_3318051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318051 prefixEnd_3318051 := by exact prefixLift 3318051
  have htrace : WordTrace (prefixWord ++ tailWord_3318051) baseStart_3318051 baseEnd_3318051 := by
    simpa [prefixWord, tailWord_3318051, baseEnd_3318051] using wordTrace_append hprefix tailTrace_3318051
  have hstable : (prefixWord ++ tailWord_3318051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318051).length < 2 ^ (prefixWord ++ tailWord_3318051).sum := by decide
  have hdescent : baseEnd_3318051 < baseStart_3318051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318105 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_3318105 : Nat := 118140960795 + 3318105 * 2 ^ 59
def prefixEnd_3318105 : Nat := 4983230072969 + 3 ^ 40 * 3318105 * 2
def baseEnd_3318105 : Nat := 1135855151391230421751879

theorem tailTrace_3318105 : CollatzResearch.WordTrace tailWord_3318105 prefixEnd_3318105 1135855151391230421751879 := by
  unfold tailWord_3318105
  simp only [CollatzResearch.WordTrace]
  refine ⟨121021231644079747062835769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80680821096053164708557179 121021231644079747062835769)
  ·
    refine ⟨90765923733059810297126827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121021231644079747062835769 90765923733059810297126827)
    ·
      refine ⟨136148885599589715445690241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90765923733059810297126827 136148885599589715445690241)
      ·
        refine ⟨102111664199692286584267681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136148885599589715445690241 102111664199692286584267681)
        ·
          refine ⟨76583748149769214938200761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102111664199692286584267681 76583748149769214938200761)
          ·
            refine ⟨57437811112326911203650571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76583748149769214938200761 57437811112326911203650571)
            ·
              refine ⟨86156716668490366805475857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57437811112326911203650571 86156716668490366805475857)
              ·
                refine ⟨64617537501367775104106893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86156716668490366805475857 64617537501367775104106893)
                ·
                  refine ⟨24231576563012915664040085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64617537501367775104106893 24231576563012915664040085)
                  ·
                    refine ⟨1135855151391230421751879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24231576563012915664040085 1135855151391230421751879)
                    ·
                      rfl

theorem cell22_3318105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_3318105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318105 prefixEnd_3318105 := by exact prefixLift 3318105
  have htrace : WordTrace (prefixWord ++ tailWord_3318105) baseStart_3318105 baseEnd_3318105 := by
    simpa [prefixWord, tailWord_3318105, baseEnd_3318105] using wordTrace_append hprefix tailTrace_3318105
  have hstable : (prefixWord ++ tailWord_3318105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318105).length < 2 ^ (prefixWord ++ tailWord_3318105).sum := by decide
  have hdescent : baseEnd_3318105 < baseStart_3318105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318124 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_3318124 : Nat := 118140960795 + 3318124 * 2 ^ 59
def prefixEnd_3318124 : Nat := 4983230072969 + 3 ^ 40 * 3318124 * 2
def baseEnd_3318124 : Nat := 1135861655479520705526821

theorem tailTrace_3318124 : CollatzResearch.WordTrace tailWord_3318124 prefixEnd_3318124 1135861655479520705526821 := by
  unfold tailWord_3318124
  simp only [CollatzResearch.WordTrace]
  refine ⟨60510962315505456653888713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80681283087340608871851617 60510962315505456653888713)
  ·
    refine ⟨45383221736629092490416535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60510962315505456653888713 45383221736629092490416535)
    ·
      refine ⟨68074832604943638735624803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45383221736629092490416535 68074832604943638735624803)
      ·
        refine ⟨102112248907415458103437205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68074832604943638735624803 102112248907415458103437205)
        ·
          refine ⟨4786511667535099598598619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102112248907415458103437205 4786511667535099598598619)
          ·
            refine ⟨7179767501302649397897929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786511667535099598598619 7179767501302649397897929)
            ·
              refine ⟨5384825625976987048423447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7179767501302649397897929 5384825625976987048423447)
              ·
                refine ⟨8077238438965480572635171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384825625976987048423447 8077238438965480572635171)
                ·
                  refine ⟨12115857658448220858952757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8077238438965480572635171 12115857658448220858952757)
                  ·
                    refine ⟨1135861655479520705526821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12115857658448220858952757 1135861655479520705526821)
                    ·
                      rfl

theorem cell22_3318124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_3318124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318124 prefixEnd_3318124 := by exact prefixLift 3318124
  have htrace : WordTrace (prefixWord ++ tailWord_3318124) baseStart_3318124 baseEnd_3318124 := by
    simpa [prefixWord, tailWord_3318124, baseEnd_3318124] using wordTrace_append hprefix tailTrace_3318124
  have hstable : (prefixWord ++ tailWord_3318124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318124).length < 2 ^ (prefixWord ++ tailWord_3318124).sum := by decide
  have hdescent : baseEnd_3318124 < baseStart_3318124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318135 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3318135 : Nat := 118140960795 + 3318135 * 2 ^ 59
def prefixEnd_3318135 : Nat := 4983230072969 + 3 ^ 40 * 3318135 * 2
def baseEnd_3318135 : Nat := 1135865421004320343501787

theorem tailTrace_3318135 : CollatzResearch.WordTrace tailWord_3318135 prefixEnd_3318135 1135865421004320343501787 := by
  unfold tailWord_3318135
  simp only [CollatzResearch.WordTrace]
  refine ⟨121022325833971062186427859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80681550555980708124285239 121022325833971062186427859)
  ·
    refine ⟨181533488750956593279641789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121022325833971062186427859 181533488750956593279641789)
    ·
      refine ⟨68075058281608722479865671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181533488750956593279641789 68075058281608722479865671)
      ·
        refine ⟨102112587422413083719798507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68075058281608722479865671 102112587422413083719798507)
        ·
          refine ⟨153168881133619625579697761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102112587422413083719798507 153168881133619625579697761)
          ·
            refine ⟨114876660850214719184773321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153168881133619625579697761 114876660850214719184773321)
            ·
              refine ⟨86157495637661039388579991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114876660850214719184773321 86157495637661039388579991)
              ·
                refine ⟨129236243456491559082869987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86157495637661039388579991 129236243456491559082869987)
                ·
                  refine ⟨193854365184737338624304981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129236243456491559082869987 193854365184737338624304981)
                  ·
                    refine ⟨1135865421004320343501787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193854365184737338624304981 1135865421004320343501787)
                    ·
                      rfl

theorem cell22_3318135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3318135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318135 prefixEnd_3318135 := by exact prefixLift 3318135
  have htrace : WordTrace (prefixWord ++ tailWord_3318135) baseStart_3318135 baseEnd_3318135 := by
    simpa [prefixWord, tailWord_3318135, baseEnd_3318135] using wordTrace_append hprefix tailTrace_3318135
  have hstable : (prefixWord ++ tailWord_3318135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318135).length < 2 ^ (prefixWord ++ tailWord_3318135).sum := by decide
  have hdescent : baseEnd_3318135 < baseStart_3318135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318139 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 2, 4]
def baseStart_3318139 : Nat := 118140960795 + 3318139 * 2 ^ 59
def prefixEnd_3318139 : Nat := 4983230072969 + 3 ^ 40 * 3318139 * 2
def baseEnd_3318139 : Nat := 1135866790286065666401775

theorem tailTrace_3318139 : CollatzResearch.WordTrace tailWord_3318139 prefixEnd_3318139 1135866790286065666401775 := by
  unfold tailWord_3318139
  simp only [CollatzResearch.WordTrace]
  refine ⟨121022471725956570869573471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80681647817304380579715647 121022471725956570869573471)
  ·
    refine ⟨181533707588934856304360207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121022471725956570869573471 181533707588934856304360207)
    ·
      refine ⟨272300561383402284456540311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181533707588934856304360207 272300561383402284456540311)
      ·
        refine ⟨408450842075103426684810467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272300561383402284456540311 408450842075103426684810467)
        ·
          refine ⟨612676263112655140027215701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408450842075103426684810467 612676263112655140027215701)
          ·
            refine ⟨3589899979175713711096967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 612676263112655140027215701 3589899979175713711096967)
            ·
              refine ⟨5384849968763570566645451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589899979175713711096967 5384849968763570566645451)
              ·
                refine ⟨8077274953145355849968177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384849968763570566645451 8077274953145355849968177)
                ·
                  refine ⟨6057956214859016887476133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8077274953145355849968177 6057956214859016887476133)
                  ·
                    refine ⟨1135866790286065666401775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6057956214859016887476133 1135866790286065666401775)
                    ·
                      rfl

theorem cell22_3318139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 4].length) (baseStart_3318139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318139 prefixEnd_3318139 := by exact prefixLift 3318139
  have htrace : WordTrace (prefixWord ++ tailWord_3318139) baseStart_3318139 baseEnd_3318139 := by
    simpa [prefixWord, tailWord_3318139, baseEnd_3318139] using wordTrace_append hprefix tailTrace_3318139
  have hstable : (prefixWord ++ tailWord_3318139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318139).length < 2 ^ (prefixWord ++ tailWord_3318139).sum := by decide
  have hdescent : baseEnd_3318139 < baseStart_3318139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318154 : List Nat := [3, 1, 2, 5, 1, 1, 9]
def baseStart_3318154 : Nat := 118140960795 + 3318154 * 2 ^ 59
def prefixEnd_3318154 : Nat := 4983230072969 + 3 ^ 40 * 3318154 * 2
def baseEnd_3318154 : Nat := 42069330558985578788027

theorem tailTrace_3318154 : CollatzResearch.WordTrace tailWord_3318154 prefixEnd_3318154 42069330558985578788027 := by
  unfold tailWord_3318154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30255754705225557107842379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80682012547268152287579677 30255754705225557107842379)
  ·
    refine ⟨45383632057838335661763569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30255754705225557107842379 45383632057838335661763569)
    ·
      refine ⟨34037724043378751746322677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45383632057838335661763569 34037724043378751746322677)
      ·
        refine ⟨3191036629066757976217751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34037724043378751746322677 3191036629066757976217751)
        ·
          refine ⟨4786554943600136964326627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191036629066757976217751 4786554943600136964326627)
          ·
            refine ⟨7179832415400205446489941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786554943600136964326627 7179832415400205446489941)
            ·
              refine ⟨42069330558985578788027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7179832415400205446489941 42069330558985578788027)
              ·
                rfl

theorem cell22_3318154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 9].length) (baseStart_3318154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318154 prefixEnd_3318154 := by exact prefixLift 3318154
  have htrace : WordTrace (prefixWord ++ tailWord_3318154) baseStart_3318154 baseEnd_3318154 := by
    simpa [prefixWord, tailWord_3318154, baseEnd_3318154] using wordTrace_append hprefix tailTrace_3318154
  have hstable : (prefixWord ++ tailWord_3318154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318154).length < 2 ^ (prefixWord ++ tailWord_3318154).sum := by decide
  have hdescent : baseEnd_3318154 < baseStart_3318154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318158 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_3318158 : Nat := 118140960795 + 3318158 * 2 ^ 59
def prefixEnd_3318158 : Nat := 4983230072969 + 3 ^ 40 * 3318158 * 2
def baseEnd_3318158 : Nat := 1135873294374355950176717

theorem tailTrace_3318158 : CollatzResearch.WordTrace tailWord_3318158 prefixEnd_3318158 1135873294374355950176717 := by
  unfold tailWord_3318158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127895589110967139314391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80682109808591824743010085 15127895589110967139314391)
  ·
    refine ⟨22691843383666450708971587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15127895589110967139314391 22691843383666450708971587)
    ·
      refine ⟨34037765075499676063457381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22691843383666450708971587 34037765075499676063457381)
      ·
        refine ⟨6382080951656189261898259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34037765075499676063457381 6382080951656189261898259)
        ·
          refine ⟨9573121427484283892847389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382080951656189261898259 9573121427484283892847389)
          ·
            refine ⟨3589920535306606459817771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9573121427484283892847389 3589920535306606459817771)
            ·
              refine ⟨5384880802959909689726657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589920535306606459817771 5384880802959909689726657)
              ·
                refine ⟨4038660602219932267294993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384880802959909689726657 4038660602219932267294993)
                ·
                  refine ⟨3028995451664949200471245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038660602219932267294993 3028995451664949200471245)
                  ·
                    refine ⟨1135873294374355950176717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028995451664949200471245 1135873294374355950176717)
                    ·
                      rfl

theorem cell22_3318158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_3318158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318158 prefixEnd_3318158 := by exact prefixLift 3318158
  have htrace : WordTrace (prefixWord ++ tailWord_3318158) baseStart_3318158 baseEnd_3318158 := by
    simpa [prefixWord, tailWord_3318158, baseEnd_3318158] using wordTrace_append hprefix tailTrace_3318158
  have hstable : (prefixWord ++ tailWord_3318158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318158).length < 2 ^ (prefixWord ++ tailWord_3318158).sum := by decide
  have hdescent : baseEnd_3318158 < baseStart_3318158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318169 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 3, 3]
def baseStart_3318169 : Nat := 118140960795 + 3318169 * 2 ^ 59
def prefixEnd_3318169 : Nat := 4983230072969 + 3 ^ 40 * 3318169 * 2
def baseEnd_3318169 : Nat := 1135877059899155588151683

theorem tailTrace_3318169 : CollatzResearch.WordTrace tailWord_3318169 prefixEnd_3318169 1135877059899155588151683 := by
  unfold tailWord_3318169
  simp only [CollatzResearch.WordTrace]
  refine ⟨121023565915847885993165561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80682377277231923995443707 121023565915847885993165561)
  ·
    refine ⟨90767674436885914494874171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121023565915847885993165561 90767674436885914494874171)
    ·
      refine ⟨136151511655328871742311257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90767674436885914494874171 136151511655328871742311257)
      ·
        refine ⟨102113633741496653806733443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136151511655328871742311257 102113633741496653806733443)
        ·
          refine ⟨153170450612244980710100165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102113633741496653806733443 153170450612244980710100165)
          ·
            refine ⟨28719459489795933883143781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153170450612244980710100165 28719459489795933883143781)
            ·
              refine ⟨5384898654336737603089459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28719459489795933883143781 5384898654336737603089459)
              ·
                refine ⟨8077347981505106404634189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384898654336737603089459 8077347981505106404634189)
                ·
                  refine ⟨3029005493064414901737821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8077347981505106404634189 3029005493064414901737821)
                  ·
                    refine ⟨1135877059899155588151683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029005493064414901737821 1135877059899155588151683)
                    ·
                      rfl

theorem cell22_3318169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_3318169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318169 prefixEnd_3318169 := by exact prefixLift 3318169
  have htrace : WordTrace (prefixWord ++ tailWord_3318169) baseStart_3318169 baseEnd_3318169 := by
    simpa [prefixWord, tailWord_3318169, baseEnd_3318169] using wordTrace_append hprefix tailTrace_3318169
  have hstable : (prefixWord ++ tailWord_3318169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318169).length < 2 ^ (prefixWord ++ tailWord_3318169).sum := by decide
  have hdescent : baseEnd_3318169 < baseStart_3318169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318220 : List Nat := [2, 2, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_3318220 : Nat := 118140960795 + 3318220 * 2 ^ 59
def prefixEnd_3318220 : Nat := 4983230072969 + 3 ^ 40 * 3318220 * 2
def baseEnd_3318220 : Nat := 1135894518241408455126527

theorem tailTrace_3318220 : CollatzResearch.WordTrace tailWord_3318220 prefixEnd_3318220 1135894518241408455126527 := by
  unfold tailWord_3318220
  simp only [CollatzResearch.WordTrace]
  refine ⟨60512713019331560851636057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80683617359108747802181409 60512713019331560851636057)
  ·
    refine ⟨45384534764498670638727043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60512713019331560851636057 45384534764498670638727043)
    ·
      refine ⟨68076802146748005958090565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45384534764498670638727043 68076802146748005958090565)
      ·
        refine ⟨12764400402515251117141981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68076802146748005958090565 12764400402515251117141981)
        ·
          refine ⟨4786650150943219168928243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12764400402515251117141981 4786650150943219168928243)
          ·
            refine ⟨7179975226414828753392365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786650150943219168928243 7179975226414828753392365)
            ·
              refine ⟨2692490709905560782522137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7179975226414828753392365 2692490709905560782522137)
              ·
                refine ⟨2019368032429170586891603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692490709905560782522137 2019368032429170586891603)
                ·
                  refine ⟨3029052048643755880337405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019368032429170586891603 3029052048643755880337405)
                  ·
                    refine ⟨1135894518241408455126527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029052048643755880337405 1135894518241408455126527)
                    ·
                      rfl

theorem cell22_3318220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_3318220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318220 prefixEnd_3318220 := by exact prefixLift 3318220
  have htrace : WordTrace (prefixWord ++ tailWord_3318220) baseStart_3318220 baseEnd_3318220 := by
    simpa [prefixWord, tailWord_3318220, baseEnd_3318220] using wordTrace_append hprefix tailTrace_3318220
  have hstable : (prefixWord ++ tailWord_3318220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318220).length < 2 ^ (prefixWord ++ tailWord_3318220).sum := by decide
  have hdescent : baseEnd_3318220 < baseStart_3318220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318396 : List Nat := [2, 2, 2, 1, 1, 2, 2, 6, 4]
def baseStart_3318396 : Nat := 118140960795 + 3318396 * 2 ^ 59
def prefixEnd_3318396 : Nat := 4983230072969 + 3 ^ 40 * 3318396 * 2
def baseEnd_3318396 : Nat := 378651588879400887575329

theorem tailTrace_3318396 : CollatzResearch.WordTrace tailWord_3318396 prefixEnd_3318396 378651588879400887575329 := by
  unfold tailWord_3318396
  simp only [CollatzResearch.WordTrace]
  refine ⟨60515922643012751880839521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80687896857350335841119361 60515922643012751880839521)
  ·
    refine ⟨45386941982259563910629641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60515922643012751880839521 45386941982259563910629641)
    ·
      refine ⟨34040206486694672932972231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45386941982259563910629641 34040206486694672932972231)
      ·
        refine ⟨51060309730042009399458347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34040206486694672932972231 51060309730042009399458347)
        ·
          refine ⟨76590464595063014099187521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51060309730042009399458347 76590464595063014099187521)
          ·
            refine ⟨57442848446297260574390641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76590464595063014099187521 57442848446297260574390641)
            ·
              refine ⟨43082136334722945430792981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57442848446297260574390641 43082136334722945430792981)
              ·
                refine ⟨2019475140690138067068421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43082136334722945430792981 2019475140690138067068421)
                ·
                  refine ⟨378651588879400887575329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019475140690138067068421 378651588879400887575329)
                  ·
                    rfl

theorem cell22_3318396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_3318396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318396 prefixEnd_3318396 := by exact prefixLift 3318396
  have htrace : WordTrace (prefixWord ++ tailWord_3318396) baseStart_3318396 baseEnd_3318396 := by
    simpa [prefixWord, tailWord_3318396, baseEnd_3318396] using wordTrace_append hprefix tailTrace_3318396
  have hstable : (prefixWord ++ tailWord_3318396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318396).length < 2 ^ (prefixWord ++ tailWord_3318396).sum := by decide
  have hdescent : baseEnd_3318396 < baseStart_3318396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318402 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3318402 : Nat := 118140960795 + 3318402 * 2 ^ 59
def prefixEnd_3318402 : Nat := 4983230072969 + 3 ^ 40 * 3318402 * 2
def baseEnd_3318402 : Nat := 378652273520273549025323

theorem tailTrace_3318402 : CollatzResearch.WordTrace tailWord_3318402 prefixEnd_3318402 378652273520273549025323 := by
  unfold tailWord_3318402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30258016031000941696599365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80688042749335844524264973 30258016031000941696599365)
  ·
    refine ⟨5673378005812676568112381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30258016031000941696599365 5673378005812676568112381)
    ·
      refine ⟨2127516752179753713042143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5673378005812676568112381 2127516752179753713042143)
      ·
        refine ⟨3191275128269630569563215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127516752179753713042143 3191275128269630569563215)
        ·
          refine ⟨4786912692404445854344823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191275128269630569563215 4786912692404445854344823)
          ·
            refine ⟨7180369038606668781517235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786912692404445854344823 7180369038606668781517235)
            ·
              refine ⟨10770553557910003172275853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7180369038606668781517235 10770553557910003172275853)
              ·
                refine ⟨4038957584216251189603445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10770553557910003172275853 4038957584216251189603445)
                ·
                  refine ⟨378652273520273549025323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4038957584216251189603445 378652273520273549025323)
                  ·
                    rfl

theorem cell22_3318402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3318402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318402 prefixEnd_3318402 := by exact prefixLift 3318402
  have htrace : WordTrace (prefixWord ++ tailWord_3318402) baseStart_3318402 baseEnd_3318402 := by
    simpa [prefixWord, tailWord_3318402, baseEnd_3318402] using wordTrace_append hprefix tailTrace_3318402
  have hstable : (prefixWord ++ tailWord_3318402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318402).length < 2 ^ (prefixWord ++ tailWord_3318402).sum := by decide
  have hdescent : baseEnd_3318402 < baseStart_3318402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318409 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_3318409 : Nat := 118140960795 + 3318409 * 2 ^ 59
def prefixEnd_3318409 : Nat := 4983230072969 + 3 ^ 40 * 3318409 * 2
def baseEnd_3318409 : Nat := 1135959216803874962150947

theorem tailTrace_3318409 : CollatzResearch.WordTrace tailWord_3318409 prefixEnd_3318409 1135959216803874962150947 := by
  unfold tailWord_3318409
  simp only [CollatzResearch.WordTrace]
  refine ⟨121032319434978406981902281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80688212956652271321268187 121032319434978406981902281)
  ·
    refine ⟨90774239576233805236426711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121032319434978406981902281 90774239576233805236426711)
    ·
      refine ⟨136161359364350707854640067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90774239576233805236426711 136161359364350707854640067)
      ·
        refine ⟨204242039046526061781960101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136161359364350707854640067 204242039046526061781960101)
        ·
          refine ⟨38295382321223636584117519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204242039046526061781960101 38295382321223636584117519)
          ·
            refine ⟨57443073481835454876176279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38295382321223636584117519 57443073481835454876176279)
            ·
              refine ⟨86164610222753182314264419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57443073481835454876176279 86164610222753182314264419)
              ·
                refine ⟨129246915334129773471396629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86164610222753182314264419 129246915334129773471396629)
                ·
                  refine ⟨6058449156287333131471717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129246915334129773471396629 6058449156287333131471717)
                  ·
                    refine ⟨1135959216803874962150947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6058449156287333131471717 1135959216803874962150947)
                    ·
                      rfl

theorem cell22_3318409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_3318409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318409 prefixEnd_3318409 := by exact prefixLift 3318409
  have htrace : WordTrace (prefixWord ++ tailWord_3318409) baseStart_3318409 baseEnd_3318409 := by
    simpa [prefixWord, tailWord_3318409, baseEnd_3318409] using wordTrace_append hprefix tailTrace_3318409
  have hstable : (prefixWord ++ tailWord_3318409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318409).length < 2 ^ (prefixWord ++ tailWord_3318409).sum := by decide
  have hdescent : baseEnd_3318409 < baseStart_3318409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318424 : List Nat := [2, 1, 2, 4, 1, 1, 1, 10]
def baseStart_3318424 : Nat := 118140960795 + 3318424 * 2 ^ 59
def prefixEnd_3318424 : Nat := 4983230072969 + 3 ^ 40 * 3318424 * 2
def baseEnd_3318424 : Nat := 126218261290046658113989

theorem tailTrace_3318424 : CollatzResearch.WordTrace tailWord_3318424 prefixEnd_3318424 126218261290046658113989 := by
  unfold tailWord_3318424
  simp only [CollatzResearch.WordTrace]
  refine ⟨60516433264962032271849163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80688577686616043029132217 60516433264962032271849163)
  ·
    refine ⟨90774649897443048407773745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60516433264962032271849163 90774649897443048407773745)
    ·
      refine ⟨68080987423082286305830309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90774649897443048407773745 68080987423082286305830309)
      ·
        refine ⟨12765185141827928682343183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68080987423082286305830309 12765185141827928682343183)
        ·
          refine ⟨19147777712741893023514775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12765185141827928682343183 19147777712741893023514775)
          ·
            refine ⟨28721666569112839535272163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19147777712741893023514775 28721666569112839535272163)
            ·
              refine ⟨43082499853669259302908245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28721666569112839535272163 43082499853669259302908245)
              ·
                refine ⟨126218261290046658113989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43082499853669259302908245 126218261290046658113989)
                ·
                  rfl

theorem cell22_3318424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_3318424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318424 prefixEnd_3318424 := by exact prefixLift 3318424
  have htrace : WordTrace (prefixWord ++ tailWord_3318424) baseStart_3318424 baseEnd_3318424 := by
    simpa [prefixWord, tailWord_3318424, baseEnd_3318424] using wordTrace_append hprefix tailTrace_3318424
  have hstable : (prefixWord ++ tailWord_3318424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318424).length < 2 ^ (prefixWord ++ tailWord_3318424).sum := by decide
  have hdescent : baseEnd_3318424 < baseStart_3318424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318445 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3318445 : Nat := 118140960795 + 3318445 * 2 ^ 59
def prefixEnd_3318445 : Nat := 4983230072969 + 3 ^ 40 * 3318445 * 2
def baseEnd_3318445 : Nat := 1135971540339582868250837

theorem tailTrace_3318445 : CollatzResearch.WordTrace tailWord_3318445 prefixEnd_3318445 1135971540339582868250837 := by
  unfold tailWord_3318445
  simp only [CollatzResearch.WordTrace]
  refine ⟨121033632462847985130212789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80689088308565323420141859 121033632462847985130212789)
  ·
    refine ⟨11346903043391998605957449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121033632462847985130212789 11346903043391998605957449)
    ·
      refine ⟨8510177282543998954468087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11346903043391998605957449 8510177282543998954468087)
      ·
        refine ⟨12765265923815998431702131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8510177282543998954468087 12765265923815998431702131)
        ·
          refine ⟨19147898885723997647553197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12765265923815998431702131 19147898885723997647553197)
          ·
            refine ⟨7180462082146499117832449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19147898885723997647553197 7180462082146499117832449)
            ·
              refine ⟨5385346561609874338374337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7180462082146499117832449 5385346561609874338374337)
              ·
                refine ⟨4039009921207405753780753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385346561609874338374337 4039009921207405753780753)
                ·
                  refine ⟨3029257440905554315335565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4039009921207405753780753 3029257440905554315335565)
                  ·
                    refine ⟨1135971540339582868250837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029257440905554315335565 1135971540339582868250837)
                    ·
                      rfl

theorem cell22_3318445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3318445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318445 prefixEnd_3318445 := by exact prefixLift 3318445
  have htrace : WordTrace (prefixWord ++ tailWord_3318445) baseStart_3318445 baseEnd_3318445 := by
    simpa [prefixWord, tailWord_3318445, baseEnd_3318445] using wordTrace_append hprefix tailTrace_3318445
  have hstable : (prefixWord ++ tailWord_3318445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318445).length < 2 ^ (prefixWord ++ tailWord_3318445).sum := by decide
  have hdescent : baseEnd_3318445 < baseStart_3318445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318477 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3318477 : Nat := 118140960795 + 3318477 * 2 ^ 59
def prefixEnd_3318477 : Nat := 4983230072969 + 3 ^ 40 * 3318477 * 2
def baseEnd_3318477 : Nat := 1135982494593545451450739

theorem tailTrace_3318477 : CollatzResearch.WordTrace tailWord_3318477 prefixEnd_3318477 1135982494593545451450739 := by
  unfold tailWord_3318477
  simp only [CollatzResearch.WordTrace]
  refine ⟨121034799598732054595377685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80689866399154703063585123 121034799598732054595377685)
  ·
    refine ⟨5673506231190565059158329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121034799598732054595377685 5673506231190565059158329)
    ·
      refine ⟨4255129673392923794368747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5673506231190565059158329 4255129673392923794368747)
      ·
        refine ⟨6382694510089385691553121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255129673392923794368747 6382694510089385691553121)
        ·
          refine ⟨4787020882567039268664841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6382694510089385691553121 4787020882567039268664841)
          ·
            refine ⟨3590265661925279451498631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4787020882567039268664841 3590265661925279451498631)
            ·
              refine ⟨5385398492887919177247947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590265661925279451498631 5385398492887919177247947)
              ·
                refine ⟨8078097739331878765871921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385398492887919177247947 8078097739331878765871921)
                ·
                  refine ⟨6058573304498909074403941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078097739331878765871921 6058573304498909074403941)
                  ·
                    refine ⟨1135982494593545451450739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6058573304498909074403941 1135982494593545451450739)
                    ·
                      rfl

theorem cell22_3318477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3318477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318477 prefixEnd_3318477 := by exact prefixLift 3318477
  have htrace : WordTrace (prefixWord ++ tailWord_3318477) baseStart_3318477 baseEnd_3318477 := by
    simpa [prefixWord, tailWord_3318477, baseEnd_3318477] using wordTrace_append hprefix tailTrace_3318477
  have hstable : (prefixWord ++ tailWord_3318477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318477).length < 2 ^ (prefixWord ++ tailWord_3318477).sum := by decide
  have hdescent : baseEnd_3318477 < baseStart_3318477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318490 : List Nat := [3, 1, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_3318490 : Nat := 118140960795 + 3318490 * 2 ^ 59
def prefixEnd_3318490 : Nat := 4983230072969 + 3 ^ 40 * 3318490 * 2
def baseEnd_3318490 : Nat := 1135986944759217750875699

theorem tailTrace_3318490 : CollatzResearch.WordTrace tailWord_3318490 prefixEnd_3318490 1135986944759217750875699 := by
  unfold tailWord_3318490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30258818436921239453900231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80690182498456638543733949 30258818436921239453900231)
  ·
    refine ⟨45388227655381859180850347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30258818436921239453900231 45388227655381859180850347)
    ·
      refine ⟨68082341483072788771275521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45388227655381859180850347 68082341483072788771275521)
      ·
        refine ⟨51061756112304591578456641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68082341483072788771275521 51061756112304591578456641)
        ·
          refine ⟨38296317084228443683842481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51061756112304591578456641 38296317084228443683842481)
          ·
            refine ⟨28722237813171332762881861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38296317084228443683842481 28722237813171332762881861)
            ·
              refine ⟨5385419589969624893040349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28722237813171332762881861 5385419589969624893040349)
              ·
                refine ⟨2019532346238609334890131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5385419589969624893040349 2019532346238609334890131)
                ·
                  refine ⟨3029298519357914002335197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019532346238609334890131 3029298519357914002335197)
                  ·
                    refine ⟨1135986944759217750875699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029298519357914002335197 1135986944759217750875699)
                    ·
                      rfl

theorem cell22_3318490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_3318490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318490 prefixEnd_3318490 := by exact prefixLift 3318490
  have htrace : WordTrace (prefixWord ++ tailWord_3318490) baseStart_3318490 baseEnd_3318490 := by
    simpa [prefixWord, tailWord_3318490, baseEnd_3318490] using wordTrace_append hprefix tailTrace_3318490
  have hstable : (prefixWord ++ tailWord_3318490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318490).length < 2 ^ (prefixWord ++ tailWord_3318490).sum := by decide
  have hdescent : baseEnd_3318490 < baseStart_3318490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318501 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3318501 : Nat := 118140960795 + 3318501 * 2 ^ 59
def prefixEnd_3318501 : Nat := 4983230072969 + 3 ^ 40 * 3318501 * 2
def baseEnd_3318501 : Nat := 1135990710284017388850665

theorem tailTrace_3318501 : CollatzResearch.WordTrace tailWord_3318501 prefixEnd_3318501 1135990710284017388850665 := by
  unfold tailWord_3318501
  simp only [CollatzResearch.WordTrace]
  refine ⟨121035674950645106694251357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80690449967096737796167571 121035674950645106694251357)
  ·
    refine ⟨45388378106491915010344259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121035674950645106694251357 45388378106491915010344259)
    ·
      refine ⟨68082567159737872515516389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45388378106491915010344259 68082567159737872515516389)
      ·
        refine ⟨12765481342450851096659323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68082567159737872515516389 12765481342450851096659323)
        ·
          refine ⟨19148222013676276644988985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12765481342450851096659323 19148222013676276644988985)
          ·
            refine ⟨14361166510257207483741739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19148222013676276644988985 14361166510257207483741739)
            ·
              refine ⟨21541749765385811225612609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14361166510257207483741739 21541749765385811225612609)
              ·
                refine ⟨16156312324039358419209457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21541749765385811225612609 16156312324039358419209457)
                ·
                  refine ⟨12117234243029518814407093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16156312324039358419209457 12117234243029518814407093)
                  ·
                    refine ⟨1135990710284017388850665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12117234243029518814407093 1135990710284017388850665)
                    ·
                      rfl

theorem cell22_3318501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3318501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318501 prefixEnd_3318501 := by exact prefixLift 3318501
  have htrace : WordTrace (prefixWord ++ tailWord_3318501) baseStart_3318501 baseEnd_3318501 := by
    simpa [prefixWord, tailWord_3318501, baseEnd_3318501] using wordTrace_append hprefix tailTrace_3318501
  have hstable : (prefixWord ++ tailWord_3318501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318501).length < 2 ^ (prefixWord ++ tailWord_3318501).sum := by decide
  have hdescent : baseEnd_3318501 < baseStart_3318501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318563 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 2, 3]
def baseStart_3318563 : Nat := 118140960795 + 3318563 * 2 ^ 59
def prefixEnd_3318563 : Nat := 4983230072969 + 3 ^ 40 * 3318563 * 2
def baseEnd_3318563 : Nat := 1136011934151069893800475

theorem tailTrace_3318563 : CollatzResearch.WordTrace tailWord_3318563 prefixEnd_3318563 1136011934151069893800475 := by
  unfold tailWord_3318563
  simp only [CollatzResearch.WordTrace]
  refine ⟨121037936276420491283008343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80691957517613660855338895 121037936276420491283008343)
  ·
    refine ⟨181556904414630736924512515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121037936276420491283008343 181556904414630736924512515)
    ·
      refine ⟨272335356621946105386768773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181556904414630736924512515 272335356621946105386768773)
      ·
        refine ⟨51062879366614894760019145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272335356621946105386768773 51062879366614894760019145)
        ·
          refine ⟨38297159524961171070014359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51062879366614894760019145 38297159524961171070014359)
          ·
            refine ⟨57445739287441756605021539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38297159524961171070014359 57445739287441756605021539)
            ·
              refine ⟨86168608931162634907532309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57445739287441756605021539 86168608931162634907532309)
              ·
                refine ⟨4039153543648248511290577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86168608931162634907532309 4039153543648248511290577)
                ·
                  refine ⟨3029365157736186383467933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4039153543648248511290577 3029365157736186383467933)
                  ·
                    refine ⟨1136011934151069893800475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029365157736186383467933 1136011934151069893800475)
                    ·
                      rfl

theorem cell22_3318563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 3].length) (baseStart_3318563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318563 prefixEnd_3318563 := by exact prefixLift 3318563
  have htrace : WordTrace (prefixWord ++ tailWord_3318563) baseStart_3318563 baseEnd_3318563 := by
    simpa [prefixWord, tailWord_3318563, baseEnd_3318563] using wordTrace_append hprefix tailTrace_3318563
  have hstable : (prefixWord ++ tailWord_3318563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318563).length < 2 ^ (prefixWord ++ tailWord_3318563).sum := by decide
  have hdescent : baseEnd_3318563 < baseStart_3318563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318565 : List Nat := [1, 3, 1, 2, 3, 1, 5, 2, 4]
def baseStart_3318565 : Nat := 118140960795 + 3318565 * 2 ^ 59
def prefixEnd_3318565 : Nat := 4983230072969 + 3 ^ 40 * 3318565 * 2
def baseEnd_3318565 : Nat := 378670872930647518416823

theorem tailTrace_3318565 : CollatzResearch.WordTrace tailWord_3318565 prefixEnd_3318565 378670872930647518416823 := by
  unfold tailWord_3318565
  simp only [CollatzResearch.WordTrace]
  refine ⟨121038009222413245624581149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80692006148275497083054099 121038009222413245624581149)
  ·
    refine ⟨45389253458404967109217931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121038009222413245624581149 45389253458404967109217931)
    ·
      refine ⟨68083880187607450663826897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45389253458404967109217931 68083880187607450663826897)
      ·
        refine ⟨51062910140705587997870173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68083880187607450663826897 51062910140705587997870173)
        ·
          refine ⟨19148591302764595499201315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51062910140705587997870173 19148591302764595499201315)
          ·
            refine ⟨28722886954146893248801973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19148591302764595499201315 28722886954146893248801973)
            ·
              refine ⟨2692770651951271242075185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28722886954146893248801973 2692770651951271242075185)
              ·
                refine ⟨2019577988963453431556389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692770651951271242075185 2019577988963453431556389)
                ·
                  refine ⟨378670872930647518416823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019577988963453431556389 378670872930647518416823)
                  ·
                    rfl

theorem cell22_3318565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_3318565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318565 prefixEnd_3318565 := by exact prefixLift 3318565
  have htrace : WordTrace (prefixWord ++ tailWord_3318565) baseStart_3318565 baseEnd_3318565 := by
    simpa [prefixWord, tailWord_3318565, baseEnd_3318565] using wordTrace_append hprefix tailTrace_3318565
  have hstable : (prefixWord ++ tailWord_3318565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318565).length < 2 ^ (prefixWord ++ tailWord_3318565).sum := by decide
  have hdescent : baseEnd_3318565 < baseStart_3318565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318606 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3318606 : Nat := 118140960795 + 3318606 * 2 ^ 59
def prefixEnd_3318606 : Nat := 4983230072969 + 3 ^ 40 * 3318606 * 2
def baseEnd_3318606 : Nat := 1136026653929832114975343

theorem tailTrace_3318606 : CollatzResearch.WordTrace tailWord_3318606 prefixEnd_3318606 1136026653929832114975343 := by
  unfold tailWord_3318606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15129938076908088703352959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80693003076843139751215781 15129938076908088703352959)
  ·
    refine ⟨22694907115362133055029439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15129938076908088703352959 22694907115362133055029439)
    ·
      refine ⟨34042360673043199582544159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22694907115362133055029439 34042360673043199582544159)
      ·
        refine ⟨51063541009564799373816239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34042360673043199582544159 51063541009564799373816239)
        ·
          refine ⟨76595311514347199060724359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51063541009564799373816239 76595311514347199060724359)
          ·
            refine ⟨114892967271520798591086539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76595311514347199060724359 114892967271520798591086539)
            ·
              refine ⟨172339450907281197886629809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114892967271520798591086539 172339450907281197886629809)
              ·
                refine ⟨129254588180460898414972357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172339450907281197886629809 129254588180460898414972357)
                ·
                  refine ⟨24235235283836418452807317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129254588180460898414972357 24235235283836418452807317)
                  ·
                    refine ⟨1136026653929832114975343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24235235283836418452807317 1136026653929832114975343)
                    ·
                      rfl

theorem cell22_3318606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3318606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318606 prefixEnd_3318606 := by exact prefixLift 3318606
  have htrace : WordTrace (prefixWord ++ tailWord_3318606) baseStart_3318606 baseEnd_3318606 := by
    simpa [prefixWord, tailWord_3318606, baseEnd_3318606] using wordTrace_append hprefix tailTrace_3318606
  have hstable : (prefixWord ++ tailWord_3318606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318606).length < 2 ^ (prefixWord ++ tailWord_3318606).sum := by decide
  have hdescent : baseEnd_3318606 < baseStart_3318606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318710 : List Nat := [5, 1, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3318710 : Nat := 118140960795 + 3318710 * 2 ^ 59
def prefixEnd_3318710 : Nat := 4983230072969 + 3 ^ 40 * 3318710 * 2
def baseEnd_3318710 : Nat := 1136062255255210510375025

theorem tailTrace_3318710 : CollatzResearch.WordTrace tailWord_3318710 prefixEnd_3318710 1136062255255210510375025 := by
  unfold tailWord_3318710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565206112930495961788099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80695531871258623592406389 7565206112930495961788099)
  ·
    refine ⟨11347809169395743942682149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7565206112930495961788099 11347809169395743942682149)
    ·
      refine ⟨2127714219261701989252903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11347809169395743942682149 2127714219261701989252903)
      ·
        refine ⟨3191571328892552983879355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127714219261701989252903 3191571328892552983879355)
        ·
          refine ⟨4787356993338829475819033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191571328892552983879355 4787356993338829475819033)
          ·
            refine ⟨3590517745004122106864275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4787356993338829475819033 3590517745004122106864275)
            ·
              refine ⟨5385776617506183160296413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590517745004122106864275 5385776617506183160296413)
              ·
                refine ⟨2019666231564818685111155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5385776617506183160296413 2019666231564818685111155)
                ·
                  refine ⟨3029499347347228027666733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019666231564818685111155 3029499347347228027666733)
                  ·
                    refine ⟨1136062255255210510375025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029499347347228027666733 1136062255255210510375025)
                    ·
                      rfl

theorem cell22_3318710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3318710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318710 prefixEnd_3318710 := by exact prefixLift 3318710
  have htrace : WordTrace (prefixWord ++ tailWord_3318710) baseStart_3318710 baseEnd_3318710 := by
    simpa [prefixWord, tailWord_3318710, baseEnd_3318710] using wordTrace_append hprefix tailTrace_3318710
  have hstable : (prefixWord ++ tailWord_3318710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318710).length < 2 ^ (prefixWord ++ tailWord_3318710).sum := by decide
  have hdescent : baseEnd_3318710 < baseStart_3318710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318713 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_3318713 : Nat := 118140960795 + 3318713 * 2 ^ 59
def prefixEnd_3318713 : Nat := 4983230072969 + 3 ^ 40 * 3318713 * 2
def baseEnd_3318713 : Nat := 1136063282216519502550015

theorem tailTrace_3318713 : CollatzResearch.WordTrace tailWord_3318713 prefixEnd_3318713 1136063282216519502550015 := by
  unfold tailWord_3318713
  simp only [CollatzResearch.WordTrace]
  refine ⟨121043407225877066900968793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80695604817251377933979195 121043407225877066900968793)
  ·
    refine ⟨90782555419407800175726595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121043407225877066900968793 90782555419407800175726595)
    ·
      refine ⟨136173833129111700263589893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90782555419407800175726595 136173833129111700263589893)
      ·
        refine ⟨25532593711708443799423105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136173833129111700263589893 25532593711708443799423105)
        ·
          refine ⟨19149445283781332849567329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25532593711708443799423105 19149445283781332849567329)
          ·
            refine ⟨14362083962835999637175497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19149445283781332849567329 14362083962835999637175497)
            ·
              refine ⟨10771562972126999727881623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14362083962835999637175497 10771562972126999727881623)
              ·
                refine ⟨16157344458190499591822435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771562972126999727881623 16157344458190499591822435)
                ·
                  refine ⟨24236016687285749387733653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16157344458190499591822435 24236016687285749387733653)
                  ·
                    refine ⟨1136063282216519502550015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24236016687285749387733653 1136063282216519502550015)
                    ·
                      rfl

theorem cell22_3318713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_3318713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318713 prefixEnd_3318713 := by exact prefixLift 3318713
  have htrace : WordTrace (prefixWord ++ tailWord_3318713) baseStart_3318713 baseEnd_3318713 := by
    simpa [prefixWord, tailWord_3318713, baseEnd_3318713] using wordTrace_append hprefix tailTrace_3318713
  have hstable : (prefixWord ++ tailWord_3318713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318713).length < 2 ^ (prefixWord ++ tailWord_3318713).sum := by decide
  have hdescent : baseEnd_3318713 < baseStart_3318713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318749 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3318749 : Nat := 118140960795 + 3318749 * 2 ^ 59
def prefixEnd_3318749 : Nat := 4983230072969 + 3 ^ 40 * 3318749 * 2
def baseEnd_3318749 : Nat := 1136075605752227408649905

theorem tailTrace_3318749 : CollatzResearch.WordTrace tailWord_3318749 prefixEnd_3318749 1136075605752227408649905 := by
  unfold tailWord_3318749
  simp only [CollatzResearch.WordTrace]
  refine ⟨121044720253746645049279301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80696480169164430032852867 121044720253746645049279301)
  ·
    refine ⟨22695885047577495946739869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121044720253746645049279301 22695885047577495946739869)
    ·
      refine ⟨8510956892841560980027451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22695885047577495946739869 8510956892841560980027451)
      ·
        refine ⟨12766435339262341470041177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8510956892841560980027451 12766435339262341470041177)
        ·
          refine ⟨9574826504446756102530883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12766435339262341470041177 9574826504446756102530883)
          ·
            refine ⟨14362239756670134153796325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574826504446756102530883 14362239756670134153796325)
            ·
              refine ⟨2692919954375650153836811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14362239756670134153796325 2692919954375650153836811)
              ·
                refine ⟨4039379931563475230755217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692919954375650153836811 4039379931563475230755217)
                ·
                  refine ⟨3029534948672606423066413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4039379931563475230755217 3029534948672606423066413)
                  ·
                    refine ⟨1136075605752227408649905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029534948672606423066413 1136075605752227408649905)
                    ·
                      rfl

theorem cell22_3318749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3318749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318749 prefixEnd_3318749 := by exact prefixLift 3318749
  have htrace : WordTrace (prefixWord ++ tailWord_3318749) baseStart_3318749 baseEnd_3318749 := by
    simpa [prefixWord, tailWord_3318749, baseEnd_3318749] using wordTrace_append hprefix tailTrace_3318749
  have hstable : (prefixWord ++ tailWord_3318749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318749).length < 2 ^ (prefixWord ++ tailWord_3318749).sum := by decide
  have hdescent : baseEnd_3318749 < baseStart_3318749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318760 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 3, 3]
def baseStart_3318760 : Nat := 118140960795 + 3318760 * 2 ^ 59
def prefixEnd_3318760 : Nat := 4983230072969 + 3 ^ 40 * 3318760 * 2
def baseEnd_3318760 : Nat := 1136079371277027046624871

theorem tailTrace_3318760 : CollatzResearch.WordTrace tailWord_3318760 prefixEnd_3318760 1136079371277027046624871 := by
  unfold tailWord_3318760
  simp only [CollatzResearch.WordTrace]
  refine ⟨60522560728353396963964867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80696747637804529285286489 60522560728353396963964867)
  ·
    refine ⟨90783841092530095445947301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60522560728353396963964867 90783841092530095445947301)
    ·
      refine ⟨17021970204849392896115119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90783841092530095445947301 17021970204849392896115119)
      ·
        refine ⟨25532955307274089344172679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17021970204849392896115119 25532955307274089344172679)
        ·
          refine ⟨38299432960911134016259019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25532955307274089344172679 38299432960911134016259019)
          ·
            refine ⟨57449149441366701024388529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38299432960911134016259019 57449149441366701024388529)
            ·
              refine ⟨43086862081025025768291397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57449149441366701024388529 43086862081025025768291397)
              ·
                refine ⟨8078786640192192331554637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43086862081025025768291397 8078786640192192331554637)
                ·
                  refine ⟨3029544990072072124332989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8078786640192192331554637 3029544990072072124332989)
                  ·
                    refine ⟨1136079371277027046624871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029544990072072124332989 1136079371277027046624871)
                    ·
                      rfl

theorem cell22_3318760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_3318760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318760 prefixEnd_3318760 := by exact prefixLift 3318760
  have htrace : WordTrace (prefixWord ++ tailWord_3318760) baseStart_3318760 baseEnd_3318760 := by
    simpa [prefixWord, tailWord_3318760, baseEnd_3318760] using wordTrace_append hprefix tailTrace_3318760
  have hstable : (prefixWord ++ tailWord_3318760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318760).length < 2 ^ (prefixWord ++ tailWord_3318760).sum := by decide
  have hdescent : baseEnd_3318760 < baseStart_3318760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318777 : List Nat := [1, 2, 1, 3, 1, 3, 2, 5, 1, 3]
def baseStart_3318777 : Nat := 118140960795 + 3318777 * 2 ^ 59
def prefixEnd_3318777 : Nat := 4983230072969 + 3 ^ 40 * 3318777 * 2
def baseEnd_3318777 : Nat := 1136085190724444668949819

theorem tailTrace_3318777 : CollatzResearch.WordTrace tailWord_3318777 prefixEnd_3318777 1136085190724444668949819 := by
  unfold tailWord_3318777
  simp only [CollatzResearch.WordTrace]
  refine ⟨121045741497645205831298585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80697160998430137220865723 121045741497645205831298585)
  ·
    refine ⟨90784306123233904373473939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121045741497645205831298585 90784306123233904373473939)
    ·
      refine ⟨136176459184850856560210909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90784306123233904373473939 136176459184850856560210909)
      ·
        refine ⟨51066172194319071210079091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136176459184850856560210909 51066172194319071210079091)
        ·
          refine ⟨76599258291478606815118637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51066172194319071210079091 76599258291478606815118637)
          ·
            refine ⟨28724721859304477555669489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76599258291478606815118637 28724721859304477555669489)
            ·
              refine ⟨21543541394478358166752117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28724721859304477555669489 21543541394478358166752117)
              ·
                refine ⟨2019707005732346078133011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21543541394478358166752117 2019707005732346078133011)
                ·
                  refine ⟨3029560508598519117199517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019707005732346078133011 3029560508598519117199517)
                  ·
                    refine ⟨1136085190724444668949819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029560508598519117199517 1136085190724444668949819)
                    ·
                      rfl

theorem cell22_3318777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 3].length) (baseStart_3318777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318777 prefixEnd_3318777 := by exact prefixLift 3318777
  have htrace : WordTrace (prefixWord ++ tailWord_3318777) baseStart_3318777 baseEnd_3318777 := by
    simpa [prefixWord, tailWord_3318777, baseEnd_3318777] using wordTrace_append hprefix tailTrace_3318777
  have hstable : (prefixWord ++ tailWord_3318777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318777).length < 2 ^ (prefixWord ++ tailWord_3318777).sum := by decide
  have hdescent : baseEnd_3318777 < baseStart_3318777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318794 : List Nat := [3, 1, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_3318794 : Nat := 118140960795 + 3318794 * 2 ^ 59
def prefixEnd_3318794 : Nat := 4983230072969 + 3 ^ 40 * 3318794 * 2
def baseEnd_3318794 : Nat := 1136091010171862291274767

theorem tailTrace_3318794 : CollatzResearch.WordTrace tailWord_3318794 prefixEnd_3318794 1136091010171862291274767 := by
  unfold tailWord_3318794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30261590384645904433666859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80697574359055745156444957 30261590384645904433666859)
  ·
    refine ⟨45392385576968856650500289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30261590384645904433666859 45392385576968856650500289)
    ·
      refine ⟨34044289182726642487875217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45392385576968856650500289 34044289182726642487875217)
      ·
        refine ⟨25533216887044981865906413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34044289182726642487875217 25533216887044981865906413)
        ·
          refine ⟨9574956332641868199714905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25533216887044981865906413 9574956332641868199714905)
          ·
            refine ⟨7181217249481401149786179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9574956332641868199714905 7181217249481401149786179)
            ·
              refine ⟨10771825874222101724679269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181217249481401149786179 10771825874222101724679269)
              ·
                refine ⟨2019717351416644073377363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10771825874222101724679269 2019717351416644073377363)
                ·
                  refine ⟨3029576027124966110066045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019717351416644073377363 3029576027124966110066045)
                  ·
                    refine ⟨1136091010171862291274767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029576027124966110066045 1136091010171862291274767)
                    ·
                      rfl

theorem cell22_3318794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_3318794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318794 prefixEnd_3318794 := by exact prefixLift 3318794
  have htrace : WordTrace (prefixWord ++ tailWord_3318794) baseStart_3318794 baseEnd_3318794 := by
    simpa [prefixWord, tailWord_3318794, baseEnd_3318794] using wordTrace_append hprefix tailTrace_3318794
  have hstable : (prefixWord ++ tailWord_3318794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318794).length < 2 ^ (prefixWord ++ tailWord_3318794).sum := by decide
  have hdescent : baseEnd_3318794 < baseStart_3318794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318805 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3318805 : Nat := 118140960795 + 3318805 * 2 ^ 59
def prefixEnd_3318805 : Nat := 4983230072969 + 3 ^ 40 * 3318805 * 2
def baseEnd_3318805 : Nat := 1136094775696661929249733

theorem tailTrace_3318805 : CollatzResearch.WordTrace tailWord_3318805 prefixEnd_3318805 1136094775696661929249733 := by
  unfold tailWord_3318805
  simp only [CollatzResearch.WordTrace]
  refine ⟨121046762741543766613317869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80697841827695844408878579 121046762741543766613317869)
  ·
    refine ⟨45392536028078912479994201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121046762741543766613317869 45392536028078912479994201)
    ·
      refine ⟨34044402021059184359995651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45392536028078912479994201 34044402021059184359995651)
      ·
        refine ⟨51066603031588776539993477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34044402021059184359995651 51066603031588776539993477)
        ·
          refine ⟨9574988068422895601248777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51066603031588776539993477 9574988068422895601248777)
          ·
            refine ⟨7181241051317171700936583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9574988068422895601248777 7181241051317171700936583)
            ·
              refine ⟨10771861576975757551404875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181241051317171700936583 10771861576975757551404875)
              ·
                refine ⟨16157792365463636327107313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771861576975757551404875 16157792365463636327107313)
                ·
                  refine ⟨12118344274097727245330485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16157792365463636327107313 12118344274097727245330485)
                  ·
                    refine ⟨1136094775696661929249733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12118344274097727245330485 1136094775696661929249733)
                    ·
                      rfl

theorem cell22_3318805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3318805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318805 prefixEnd_3318805 := by exact prefixLift 3318805
  have htrace : WordTrace (prefixWord ++ tailWord_3318805) baseStart_3318805 baseEnd_3318805 := by
    simpa [prefixWord, tailWord_3318805, baseEnd_3318805] using wordTrace_append hprefix tailTrace_3318805
  have hstable : (prefixWord ++ tailWord_3318805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318805).length < 2 ^ (prefixWord ++ tailWord_3318805).sum := by decide
  have hdescent : baseEnd_3318805 < baseStart_3318805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318882 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3318882 : Nat := 118140960795 + 3318882 * 2 ^ 59
def prefixEnd_3318882 : Nat := 4983230072969 + 3 ^ 40 * 3318882 * 2
def baseEnd_3318882 : Nat := 1136121134370259395074497

theorem tailTrace_3318882 : CollatzResearch.WordTrace tailWord_3318882 prefixEnd_3318882 1136121134370259395074497 := by
  unfold tailWord_3318882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30262392790566202190967725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80699714108176539175913933 30262392790566202190967725)
  ·
    refine ⟨11348397296462325821612897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30262392790566202190967725 11348397296462325821612897)
    ·
      refine ⟨8511297972346744366209673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11348397296462325821612897 8511297972346744366209673)
      ·
        refine ⟨6383473479260058274657255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8511297972346744366209673 6383473479260058274657255)
        ·
          refine ⟨9575210218890087411985883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6383473479260058274657255 9575210218890087411985883)
          ·
            refine ⟨14362815328335131117978825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9575210218890087411985883 14362815328335131117978825)
            ·
              refine ⟨10772111496251348338484119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14362815328335131117978825 10772111496251348338484119)
              ·
                refine ⟨16158167244377022507726179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10772111496251348338484119 16158167244377022507726179)
                ·
                  refine ⟨24237250866565533761589269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16158167244377022507726179 24237250866565533761589269)
                  ·
                    refine ⟨1136121134370259395074497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24237250866565533761589269 1136121134370259395074497)
                    ·
                      rfl

theorem cell22_3318882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3318882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318882 prefixEnd_3318882 := by exact prefixLift 3318882
  have htrace : WordTrace (prefixWord ++ tailWord_3318882) baseStart_3318882 baseEnd_3318882 := by
    simpa [prefixWord, tailWord_3318882, baseEnd_3318882] using wordTrace_append hprefix tailTrace_3318882
  have hstable : (prefixWord ++ tailWord_3318882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318882).length < 2 ^ (prefixWord ++ tailWord_3318882).sum := by decide
  have hdescent : baseEnd_3318882 < baseStart_3318882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318912 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 3, 3]
def baseStart_3318912 : Nat := 118140960795 + 3318912 * 2 ^ 59
def prefixEnd_3318912 : Nat := 4983230072969 + 3 ^ 40 * 3318912 * 2
def baseEnd_3318912 : Nat := 1136131403983349316824405

theorem tailTrace_3318912 : CollatzResearch.WordTrace tailWord_3318912 prefixEnd_3318912 1136131403983349316824405 := by
  unfold tailWord_3318912
  simp only [CollatzResearch.WordTrace]
  refine ⟨60525332676078061943731495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80700443568104082591641993 60525332676078061943731495)
  ·
    refine ⟨90787999014117092915597243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60525332676078061943731495 90787999014117092915597243)
    ·
      refine ⟨136181998521175639373395865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90787999014117092915597243 136181998521175639373395865)
      ·
        refine ⟨102136498890881729530046899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136181998521175639373395865 102136498890881729530046899)
        ·
          refine ⟨153204748336322594295070349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102136498890881729530046899 153204748336322594295070349)
          ·
            refine ⟨57451780626120972860651381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153204748336322594295070349 57451780626120972860651381)
            ·
              refine ⟨5386104433698841205686067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57451780626120972860651381 5386104433698841205686067)
              ·
                refine ⟨8079156650548261808529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386104433698841205686067 8079156650548261808529101)
                ·
                  refine ⟨3029683743955598178198413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8079156650548261808529101 3029683743955598178198413)
                  ·
                    refine ⟨1136131403983349316824405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029683743955598178198413 1136131403983349316824405)
                    ·
                      rfl

theorem cell22_3318912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_3318912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318912 prefixEnd_3318912 := by exact prefixLift 3318912
  have htrace : WordTrace (prefixWord ++ tailWord_3318912) baseStart_3318912 baseEnd_3318912 := by
    simpa [prefixWord, tailWord_3318912, baseEnd_3318912] using wordTrace_append hprefix tailTrace_3318912
  have hstable : (prefixWord ++ tailWord_3318912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318912).length < 2 ^ (prefixWord ++ tailWord_3318912).sum := by decide
  have hdescent : baseEnd_3318912 < baseStart_3318912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318970 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_3318970 : Nat := 118140960795 + 3318970 * 2 ^ 59
def prefixEnd_3318970 : Nat := 4983230072969 + 3 ^ 40 * 3318970 * 2
def baseEnd_3318970 : Nat := 378717086189552166291409

theorem tailTrace_3318970 : CollatzResearch.WordTrace tailWord_3318970 prefixEnd_3318970 378717086189552166291409 := by
  unfold tailWord_3318970
  simp only [CollatzResearch.WordTrace]
  refine ⟨30263195196486499948268591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80701853857297333195382909 30263195196486499948268591)
  ·
    refine ⟨45394792794729749922402887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30263195196486499948268591 45394792794729749922402887)
    ·
      refine ⟨68092189192094624883604331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45394792794729749922402887 68092189192094624883604331)
      ·
        refine ⟨102138283788141937325406497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68092189192094624883604331 102138283788141937325406497)
        ·
          refine ⟨76603712841106452994054873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102138283788141937325406497 76603712841106452994054873)
          ·
            refine ⟨57452784630829839745541155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76603712841106452994054873 57452784630829839745541155)
            ·
              refine ⟨86179176946244759618311733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57452784630829839745541155 86179176946244759618311733)
              ·
                refine ⟨8079297838710446214216725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86179176946244759618311733 8079297838710446214216725)
                ·
                  refine ⟨378717086189552166291409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8079297838710446214216725 378717086189552166291409)
                  ·
                    rfl

theorem cell22_3318970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_3318970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318970 prefixEnd_3318970 := by exact prefixLift 3318970
  have htrace : WordTrace (prefixWord ++ tailWord_3318970) baseStart_3318970 baseEnd_3318970 := by
    simpa [prefixWord, tailWord_3318970, baseEnd_3318970] using wordTrace_append hprefix tailTrace_3318970
  have hstable : (prefixWord ++ tailWord_3318970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318970).length < 2 ^ (prefixWord ++ tailWord_3318970).sum := by decide
  have hdescent : baseEnd_3318970 < baseStart_3318970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318972 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_3318972 : Nat := 118140960795 + 3318972 * 2 ^ 59
def prefixEnd_3318972 : Nat := 4983230072969 + 3 ^ 40 * 3318972 * 2
def baseEnd_3318972 : Nat := 1136151943209529160324221

theorem tailTrace_3318972 : CollatzResearch.WordTrace tailWord_3318972 prefixEnd_3318972 1136151943209529160324221 := by
  unfold tailWord_3318972
  simp only [CollatzResearch.WordTrace]
  refine ⟨60526426865969377067323585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80701902487959169423098113 60526426865969377067323585)
  ·
    refine ⟨45394820149477032800492689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60526426865969377067323585 45394820149477032800492689)
    ·
      refine ⟨34046115112107774600369517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45394820149477032800492689 34046115112107774600369517)
      ·
        refine ⟨12767293167040415475138569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34046115112107774600369517 12767293167040415475138569)
        ·
          refine ⟨9575469875280311606353927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12767293167040415475138569 9575469875280311606353927)
          ·
            refine ⟨14363204812920467409530891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9575469875280311606353927 14363204812920467409530891)
            ·
              refine ⟨21544807219380701114296337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14363204812920467409530891 21544807219380701114296337)
              ·
                refine ⟨16158605414535525835722253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21544807219380701114296337 16158605414535525835722253)
                ·
                  refine ⟨6059477030450822188395845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16158605414535525835722253 6059477030450822188395845)
                  ·
                    refine ⟨1136151943209529160324221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6059477030450822188395845 1136151943209529160324221)
                    ·
                      rfl

theorem cell22_3318972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_3318972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3318972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3318972 prefixEnd_3318972 := by exact prefixLift 3318972
  have htrace : WordTrace (prefixWord ++ tailWord_3318972) baseStart_3318972 baseEnd_3318972 := by
    simpa [prefixWord, tailWord_3318972, baseEnd_3318972] using wordTrace_append hprefix tailTrace_3318972
  have hstable : (prefixWord ++ tailWord_3318972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318972).length < 2 ^ (prefixWord ++ tailWord_3318972).sum := by decide
  have hdescent : baseEnd_3318972 < baseStart_3318972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319002 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_3319002 : Nat := 118140960795 + 3319002 * 2 ^ 59
def prefixEnd_3319002 : Nat := 4983230072969 + 3 ^ 40 * 3319002 * 2
def baseEnd_3319002 : Nat := 1136162212822619082074129

theorem tailTrace_3319002 : CollatzResearch.WordTrace tailWord_3319002 prefixEnd_3319002 1136162212822619082074129 := by
  unfold tailWord_3319002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30263486980457517314559815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80702631947886712838826173 30263486980457517314559815)
  ·
    refine ⟨45395230470686275971839723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30263486980457517314559815 45395230470686275971839723)
    ·
      refine ⟨68092845706029413957759585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45395230470686275971839723 68092845706029413957759585)
      ·
        refine ⟨51069634279522060468319689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68092845706029413957759585 51069634279522060468319689)
        ·
          refine ⟨38302225709641545351239767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51069634279522060468319689 38302225709641545351239767)
          ·
            refine ⟨57453338564462318026859651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38302225709641545351239767 57453338564462318026859651)
            ·
              refine ⟨86180007846693477040289477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57453338564462318026859651 86180007846693477040289477)
              ·
                refine ⟨16158751471255026945054277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86180007846693477040289477 16158751471255026945054277)
                ·
                  refine ⟨3029765900860317552197677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16158751471255026945054277 3029765900860317552197677)
                  ·
                    refine ⟨1136162212822619082074129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029765900860317552197677 1136162212822619082074129)
                    ·
                      rfl

theorem cell22_3319002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_3319002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319002 prefixEnd_3319002 := by exact prefixLift 3319002
  have htrace : WordTrace (prefixWord ++ tailWord_3319002) baseStart_3319002 baseEnd_3319002 := by
    simpa [prefixWord, tailWord_3319002, baseEnd_3319002] using wordTrace_append hprefix tailTrace_3319002
  have hstable : (prefixWord ++ tailWord_3319002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319002).length < 2 ^ (prefixWord ++ tailWord_3319002).sum := by decide
  have hdescent : baseEnd_3319002 < baseStart_3319002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319019 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 2, 3]
def baseStart_3319019 : Nat := 118140960795 + 3319019 * 2 ^ 59
def prefixEnd_3319019 : Nat := 4983230072969 + 3 ^ 40 * 3319019 * 2
def baseEnd_3319019 : Nat := 1136168032270036704399077

theorem tailTrace_3319019 : CollatzResearch.WordTrace tailWord_3319019 prefixEnd_3319019 1136168032270036704399077 := by
  unfold tailWord_3319019
  simp only [CollatzResearch.WordTrace]
  refine ⟨121054567962768481161608111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80703045308512320774405407 121054567962768481161608111)
  ·
    refine ⟨181581851944152721742412167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121054567962768481161608111 181581851944152721742412167)
    ·
      refine ⟨272372777916229082613618251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181581851944152721742412167 272372777916229082613618251)
      ·
        refine ⟨408559166874343623920427377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272372777916229082613618251 408559166874343623920427377)
        ·
          refine ⟨306419375155757717940320533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408559166874343623920427377 306419375155757717940320533)
          ·
            refine ⟨14363408210426143028452525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 306419375155757717940320533 14363408210426143028452525)
            ·
              refine ⟨5386278078909803635669697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14363408210426143028452525 5386278078909803635669697)
              ·
                refine ⟨4039708559182352726752273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5386278078909803635669697 4039708559182352726752273)
                ·
                  refine ⟨3029781419386764545064205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4039708559182352726752273 3029781419386764545064205)
                  ·
                    refine ⟨1136168032270036704399077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029781419386764545064205 1136168032270036704399077)
                    ·
                      rfl

theorem cell22_3319019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 3].length) (baseStart_3319019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319019 prefixEnd_3319019 := by exact prefixLift 3319019
  have htrace : WordTrace (prefixWord ++ tailWord_3319019) baseStart_3319019 baseEnd_3319019 := by
    simpa [prefixWord, tailWord_3319019, baseEnd_3319019] using wordTrace_append hprefix tailTrace_3319019
  have hstable : (prefixWord ++ tailWord_3319019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319019).length < 2 ^ (prefixWord ++ tailWord_3319019).sum := by decide
  have hdescent : baseEnd_3319019 < baseStart_3319019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319036 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_3319036 : Nat := 118140960795 + 3319036 * 2 ^ 59
def prefixEnd_3319036 : Nat := 4983230072969 + 3 ^ 40 * 3319036 * 2
def baseEnd_3319036 : Nat := 1136173851717454326724025

theorem tailTrace_3319036 : CollatzResearch.WordTrace tailWord_3319036 prefixEnd_3319036 1136173851717454326724025 := by
  unfold tailWord_3319036
  simp only [CollatzResearch.WordTrace]
  refine ⟨60527594001853446532488481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80703458669137928709984641 60527594001853446532488481)
  ·
    refine ⟨45395695501390084899366361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60527594001853446532488481 45395695501390084899366361)
    ·
      refine ⟨34046771626042563674524771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45395695501390084899366361 34046771626042563674524771)
      ·
        refine ⟨51070157439063845511787157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34046771626042563674524771 51070157439063845511787157)
        ·
          refine ⟨2393913629956117758365023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51070157439063845511787157 2393913629956117758365023)
          ·
            refine ⟨3590870444934176637547535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393913629956117758365023 3590870444934176637547535)
            ·
              refine ⟨5386305667401264956321303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590870444934176637547535 5386305667401264956321303)
              ·
                refine ⟨8079458501101897434481955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386305667401264956321303 8079458501101897434481955)
                ·
                  refine ⟨12119187751652846151722933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079458501101897434481955 12119187751652846151722933)
                  ·
                    refine ⟨1136173851717454326724025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12119187751652846151722933 1136173851717454326724025)
                    ·
                      rfl

theorem cell22_3319036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_3319036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319036 prefixEnd_3319036 := by exact prefixLift 3319036
  have htrace : WordTrace (prefixWord ++ tailWord_3319036) baseStart_3319036 baseEnd_3319036 := by
    simpa [prefixWord, tailWord_3319036, baseEnd_3319036] using wordTrace_append hprefix tailTrace_3319036
  have hstable : (prefixWord ++ tailWord_3319036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319036).length < 2 ^ (prefixWord ++ tailWord_3319036).sum := by decide
  have hdescent : baseEnd_3319036 < baseStart_3319036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319077 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 7]
def baseStart_3319077 : Nat := 118140960795 + 3319077 * 2 ^ 59
def prefixEnd_3319077 : Nat := 4983230072969 + 3 ^ 40 * 3319077 * 2
def baseEnd_3319077 : Nat := 378729295618447962149633

theorem tailTrace_3319077 : CollatzResearch.WordTrace tailWord_3319077 prefixEnd_3319077 378729295618447962149633 := by
  unfold tailWord_3319077
  simp only [CollatzResearch.WordTrace]
  refine ⟨121056683396558357067219485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80704455597705571378146323 121056683396558357067219485)
  ·
    refine ⟨45396256273709383900207307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121056683396558357067219485 45396256273709383900207307)
    ·
      refine ⟨68094384410564075850310961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45396256273709383900207307 68094384410564075850310961)
      ·
        refine ⟨51070788307923056887733221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68094384410564075850310961 51070788307923056887733221)
        ·
          refine ⟨9575772807735573166449979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51070788307923056887733221 9575772807735573166449979)
          ·
            refine ⟨14363659211603359749674969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9575772807735573166449979 14363659211603359749674969)
            ·
              refine ⟨10772744408702519812256227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14363659211603359749674969 10772744408702519812256227)
              ·
                refine ⟨16159116613053779718384341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10772744408702519812256227 16159116613053779718384341)
                ·
                  refine ⟨378729295618447962149633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16159116613053779718384341 378729295618447962149633)
                  ·
                    rfl

theorem cell22_3319077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_3319077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319077 prefixEnd_3319077 := by exact prefixLift 3319077
  have htrace : WordTrace (prefixWord ++ tailWord_3319077) baseStart_3319077 baseEnd_3319077 := by
    simpa [prefixWord, tailWord_3319077, baseEnd_3319077] using wordTrace_append hprefix tailTrace_3319077
  have hstable : (prefixWord ++ tailWord_3319077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319077).length < 2 ^ (prefixWord ++ tailWord_3319077).sum := by decide
  have hdescent : baseEnd_3319077 < baseStart_3319077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319152 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_3319152 : Nat := 118140960795 + 3319152 * 2 ^ 59
def prefixEnd_3319152 : Nat := 4983230072969 + 3 ^ 40 * 3319152 * 2
def baseEnd_3319152 : Nat := 1136213560888068690823669

theorem tailTrace_3319152 : CollatzResearch.WordTrace tailWord_3319152 prefixEnd_3319152 1136213560888068690823669 := by
  unfold tailWord_3319152
  simp only [CollatzResearch.WordTrace]
  refine ⟨60529709435643322438099855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80706279247524429917466473 60529709435643322438099855)
  ·
    refine ⟨90794564153464983657149783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60529709435643322438099855 90794564153464983657149783)
    ·
      refine ⟨136191846230197475485724675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90794564153464983657149783 136191846230197475485724675)
      ·
        refine ⟨204287769345296213228587013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136191846230197475485724675 204287769345296213228587013)
        ·
          refine ⟨38303956752243039980360065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204287769345296213228587013 38303956752243039980360065)
          ·
            refine ⟨28727967564182279985270049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38303956752243039980360065 28727967564182279985270049)
            ·
              refine ⟨21545975673136709988952537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28727967564182279985270049 21545975673136709988952537)
              ·
                refine ⟨16159481754852532491714403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21545975673136709988952537 16159481754852532491714403)
                ·
                  refine ⟨24239222632278798737571605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16159481754852532491714403 24239222632278798737571605)
                  ·
                    refine ⟨1136213560888068690823669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24239222632278798737571605 1136213560888068690823669)
                    ·
                      rfl

theorem cell22_3319152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_3319152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319152 prefixEnd_3319152 := by exact prefixLift 3319152
  have htrace : WordTrace (prefixWord ++ tailWord_3319152) baseStart_3319152 baseEnd_3319152 := by
    simpa [prefixWord, tailWord_3319152, baseEnd_3319152] using wordTrace_append hprefix tailTrace_3319152
  have hstable : (prefixWord ++ tailWord_3319152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319152).length < 2 ^ (prefixWord ++ tailWord_3319152).sum := by decide
  have hdescent : baseEnd_3319152 < baseStart_3319152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319154 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_3319154 : Nat := 118140960795 + 3319154 * 2 ^ 59
def prefixEnd_3319154 : Nat := 4983230072969 + 3 ^ 40 * 3319154 * 2
def baseEnd_3319154 : Nat := 1136214245528941352273663

theorem tailTrace_3319154 : CollatzResearch.WordTrace tailWord_3319154 prefixEnd_3319154 1136214245528941352273663 := by
  unfold tailWord_3319154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30264872954319849804443129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80706327878186266145181677 30264872954319849804443129)
  ·
    refine ⟨22698654715739887353332347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30264872954319849804443129 22698654715739887353332347)
    ·
      refine ⟨34047982073609831029998521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22698654715739887353332347 34047982073609831029998521)
      ·
        refine ⟨25535986555207373272498891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34047982073609831029998521 25535986555207373272498891)
        ·
          refine ⟨38303979832811059908748337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25535986555207373272498891 38303979832811059908748337)
          ·
            refine ⟨28727984874608294931561253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38303979832811059908748337 28727984874608294931561253)
            ·
              refine ⟨5386497163989055299667735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28727984874608294931561253 5386497163989055299667735)
              ·
                refine ⟨8079745745983582949501603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386497163989055299667735 8079745745983582949501603)
                ·
                  refine ⟨12119618618975374424252405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079745745983582949501603 12119618618975374424252405)
                  ·
                    refine ⟨1136214245528941352273663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12119618618975374424252405 1136214245528941352273663)
                    ·
                      rfl

theorem cell22_3319154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_3319154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319154 prefixEnd_3319154 := by exact prefixLift 3319154
  have htrace : WordTrace (prefixWord ++ tailWord_3319154) baseStart_3319154 baseEnd_3319154 := by
    simpa [prefixWord, tailWord_3319154, baseEnd_3319154] using wordTrace_append hprefix tailTrace_3319154
  have hstable : (prefixWord ++ tailWord_3319154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319154).length < 2 ^ (prefixWord ++ tailWord_3319154).sum := by decide
  have hdescent : baseEnd_3319154 < baseStart_3319154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319188 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3319188 : Nat := 118140960795 + 3319188 * 2 ^ 59
def prefixEnd_3319188 : Nat := 4983230072969 + 3 ^ 40 * 3319188 * 2
def baseEnd_3319188 : Nat := 1136225884423776596923559

theorem tailTrace_3319188 : CollatzResearch.WordTrace tailWord_3319188 prefixEnd_3319188 1136225884423776596923559 := by
  unfold tailWord_3319188
  simp only [CollatzResearch.WordTrace]
  refine ⟨60530365949578111512255109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80707154599437482016340145 60530365949578111512255109)
  ·
    refine ⟨11349443615545895908547833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60530365949578111512255109 11349443615545895908547833)
    ·
      refine ⟨8512082711659421931410875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11349443615545895908547833 8512082711659421931410875)
      ·
        refine ⟨12768124067489132897116313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8512082711659421931410875 12768124067489132897116313)
        ·
          refine ⟨9576093050616849672837235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12768124067489132897116313 9576093050616849672837235)
          ·
            refine ⟨14364139575925274509255853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9576093050616849672837235 14364139575925274509255853)
            ·
              refine ⟨5386552340971977940970945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14364139575925274509255853 5386552340971977940970945)
              ·
                refine ⟨4039914255728983455728209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5386552340971977940970945 4039914255728983455728209)
                ·
                  refine ⟨3029935691796737591796157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4039914255728983455728209 3029935691796737591796157)
                  ·
                    refine ⟨1136225884423776596923559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3029935691796737591796157 1136225884423776596923559)
                    ·
                      rfl

theorem cell22_3319188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3319188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319188 prefixEnd_3319188 := by exact prefixLift 3319188
  have htrace : WordTrace (prefixWord ++ tailWord_3319188) baseStart_3319188 baseEnd_3319188 := by
    simpa [prefixWord, tailWord_3319188, baseEnd_3319188] using wordTrace_append hprefix tailTrace_3319188
  have hstable : (prefixWord ++ tailWord_3319188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319188).length < 2 ^ (prefixWord ++ tailWord_3319188).sum := by decide
  have hdescent : baseEnd_3319188 < baseStart_3319188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319293 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_3319293 : Nat := 118140960795 + 3319293 * 2 ^ 59
def prefixEnd_3319293 : Nat := 4983230072969 + 3 ^ 40 * 3319293 * 2
def baseEnd_3319293 : Nat := 1136261828069591323048237

theorem tailTrace_3319293 : CollatzResearch.WordTrace tailWord_3319293 prefixEnd_3319293 1136261828069591323048237 := by
  unfold tailWord_3319293
  simp only [CollatzResearch.WordTrace]
  refine ⟨121064561563775825957082533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80709707709183883971388355 121064561563775825957082533)
  ·
    refine ⟨22699605293207967366952975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121064561563775825957082533 22699605293207967366952975)
    ·
      refine ⟨34049407939811951050429463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22699605293207967366952975 34049407939811951050429463)
      ·
        refine ⟨51074111909717926575644195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34049407939811951050429463 51074111909717926575644195)
        ·
          refine ⟨76611167864576889863466293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51074111909717926575644195 76611167864576889863466293)
          ·
            refine ⟨7182296987304083424699965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76611167864576889863466293 7182296987304083424699965)
            ·
              refine ⟨2693361370239031284262487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7182296987304083424699965 2693361370239031284262487)
              ·
                refine ⟨4040042055358546926393731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693361370239031284262487 4040042055358546926393731)
                ·
                  refine ⟨6060063083037820389590597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040042055358546926393731 6060063083037820389590597)
                  ·
                    refine ⟨1136261828069591323048237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6060063083037820389590597 1136261828069591323048237)
                    ·
                      rfl

theorem cell22_3319293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_3319293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319293 prefixEnd_3319293 := by exact prefixLift 3319293
  have htrace : WordTrace (prefixWord ++ tailWord_3319293) baseStart_3319293 baseEnd_3319293 := by
    simpa [prefixWord, tailWord_3319293, baseEnd_3319293] using wordTrace_append hprefix tailTrace_3319293
  have hstable : (prefixWord ++ tailWord_3319293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319293).length < 2 ^ (prefixWord ++ tailWord_3319293).sum := by decide
  have hdescent : baseEnd_3319293 < baseStart_3319293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319308 : List Nat := [2, 2, 1, 2, 5, 1, 1, 4, 4]
def baseStart_3319308 : Nat := 118140960795 + 3319308 * 2 ^ 59
def prefixEnd_3319308 : Nat := 4983230072969 + 3 ^ 40 * 3319308 * 2
def baseEnd_3319308 : Nat := 378755654292045427974397

theorem tailTrace_3319308 : CollatzResearch.WordTrace tailWord_3319308 prefixEnd_3319308 378755654292045427974397 := by
  unfold tailWord_3319308
  simp only [CollatzResearch.WordTrace]
  refine ⟨60532554329360741759439289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80710072439147655679252385 60532554329360741759439289)
  ·
    refine ⟨45399415747020556319579467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60532554329360741759439289 45399415747020556319579467)
    ·
      refine ⟨68099123620530834479369201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45399415747020556319579467 68099123620530834479369201)
      ·
        refine ⟨51074342715398125859526901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68099123620530834479369201 51074342715398125859526901)
        ·
          refine ⟨4788219629568574299330647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51074342715398125859526901 4788219629568574299330647)
          ·
            refine ⟨7182329444352861448995971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788219629568574299330647 7182329444352861448995971)
            ·
              refine ⟨10773494166529292173493957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182329444352861448995971 10773494166529292173493957)
              ·
                refine ⟨2020030156224242282530117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10773494166529292173493957 2020030156224242282530117)
                ·
                  refine ⟨378755654292045427974397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2020030156224242282530117 378755654292045427974397)
                  ·
                    rfl

theorem cell22_3319308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_3319308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319308 prefixEnd_3319308 := by exact prefixLift 3319308
  have htrace : WordTrace (prefixWord ++ tailWord_3319308) baseStart_3319308 baseEnd_3319308 := by
    simpa [prefixWord, tailWord_3319308, baseEnd_3319308] using wordTrace_append hprefix tailTrace_3319308
  have hstable : (prefixWord ++ tailWord_3319308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319308).length < 2 ^ (prefixWord ++ tailWord_3319308).sum := by decide
  have hdescent : baseEnd_3319308 < baseStart_3319308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319357 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_3319357 : Nat := 118140960795 + 3319357 * 2 ^ 59
def prefixEnd_3319357 : Nat := 4983230072969 + 3 ^ 40 * 3319357 * 2
def baseEnd_3319357 : Nat := 1136283736577516489448041

theorem tailTrace_3319357 : CollatzResearch.WordTrace tailWord_3319357 prefixEnd_3319357 1136283736577516489448041 := by
  unfold tailWord_3319357
  simp only [CollatzResearch.WordTrace]
  refine ⟨121066895835543964887412325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80711263890362643258274883 121066895835543964887412325)
  ·
    refine ⟨22700042969164493416389811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121066895835543964887412325 22700042969164493416389811)
    ·
      refine ⟨34050064453746740124584717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22700042969164493416389811 34050064453746740124584717)
      ·
        refine ⟨12768774170155027546719269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34050064453746740124584717 12768774170155027546719269)
        ·
          refine ⟨2394145156904067665009863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12768774170155027546719269 2394145156904067665009863)
          ·
            refine ⟨3591217735356101497514795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394145156904067665009863 3591217735356101497514795)
            ·
              refine ⟨5386826603034152246272193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591217735356101497514795 5386826603034152246272193)
              ·
                refine ⟨4040119952275614184704145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5386826603034152246272193 4040119952275614184704145)
                ·
                  refine ⟨3030089964206710638528109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040119952275614184704145 3030089964206710638528109)
                  ·
                    refine ⟨1136283736577516489448041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030089964206710638528109 1136283736577516489448041)
                    ·
                      rfl

theorem cell22_3319357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_3319357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319357 prefixEnd_3319357 := by exact prefixLift 3319357
  have htrace : WordTrace (prefixWord ++ tailWord_3319357) baseStart_3319357 baseEnd_3319357 := by
    simpa [prefixWord, tailWord_3319357, baseEnd_3319357] using wordTrace_append hprefix tailTrace_3319357
  have hstable : (prefixWord ++ tailWord_3319357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319357).length < 2 ^ (prefixWord ++ tailWord_3319357).sum := by decide
  have hdescent : baseEnd_3319357 < baseStart_3319357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319402 : List Nat := [3, 1, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_3319402 : Nat := 118140960795 + 3319402 * 2 ^ 59
def prefixEnd_3319402 : Nat := 4983230072969 + 3 ^ 40 * 3319402 * 2
def baseEnd_3319402 : Nat := 1136299140997151372072903

theorem tailTrace_3319402 : CollatzResearch.WordTrace tailWord_3319402 prefixEnd_3319402 1136299140997151372072903 := by
  unfold tailWord_3319402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30267134280095234393200115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80712358080253958381866973 30267134280095234393200115)
  ·
    refine ⟨45400701420142851589800173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30267134280095234393200115 45400701420142851589800173)
    ·
      refine ⟨17025263032553569346175065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45400701420142851589800173 17025263032553569346175065)
      ·
        refine ⟨12768947274415177009631299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17025263032553569346175065 12768947274415177009631299)
        ·
          refine ⟨19153420911622765514446949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12768947274415177009631299 19153420911622765514446949)
          ·
            refine ⟨3591266420929268533958803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19153420911622765514446949 3591266420929268533958803)
            ·
              refine ⟨5386899631393902800938205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591266420929268533958803 5386899631393902800938205)
              ·
                refine ⟨2020087361772713550351827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5386899631393902800938205 2020087361772713550351827)
                ·
                  refine ⟨3030131042659070325527741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020087361772713550351827 3030131042659070325527741)
                  ·
                    refine ⟨1136299140997151372072903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030131042659070325527741 1136299140997151372072903)
                    ·
                      rfl

theorem cell22_3319402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_3319402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319402 prefixEnd_3319402 := by exact prefixLift 3319402
  have htrace : WordTrace (prefixWord ++ tailWord_3319402) baseStart_3319402 baseEnd_3319402 := by
    simpa [prefixWord, tailWord_3319402, baseEnd_3319402] using wordTrace_append hprefix tailTrace_3319402
  have hstable : (prefixWord ++ tailWord_3319402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319402).length < 2 ^ (prefixWord ++ tailWord_3319402).sum := by decide
  have hdescent : baseEnd_3319402 < baseStart_3319402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319409 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 8]
def baseStart_3319409 : Nat := 118140960795 + 3319409 * 2 ^ 59
def prefixEnd_3319409 : Nat := 4983230072969 + 3 ^ 40 * 3319409 * 2
def baseEnd_3319409 : Nat := 378767179080068562382627

theorem tailTrace_3319409 : CollatzResearch.WordTrace tailWord_3319409 prefixEnd_3319409 378767179080068562382627 := by
  unfold tailWord_3319409
  simp only [CollatzResearch.WordTrace]
  refine ⟨121068792431355577768305281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80712528287570385178870187 121068792431355577768305281)
  ·
    refine ⟨90801594323516683326228961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121068792431355577768305281 90801594323516683326228961)
    ·
      refine ⟨68101195742637512494671721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90801594323516683326228961 68101195742637512494671721)
      ·
        refine ⟨51075896806978134371003791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68101195742637512494671721 51075896806978134371003791)
        ·
          refine ⟨76613845210467201556505687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51075896806978134371003791 76613845210467201556505687)
          ·
            refine ⟨114920767815700802334758531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76613845210467201556505687 114920767815700802334758531)
            ·
              refine ⟨172381151723551203502137797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114920767815700802334758531 172381151723551203502137797)
              ·
                refine ⟨32321465948165850656650837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172381151723551203502137797 32321465948165850656650837)
                ·
                  refine ⟨378767179080068562382627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32321465948165850656650837 378767179080068562382627)
                  ·
                    rfl

theorem cell22_3319409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_3319409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319409 prefixEnd_3319409 := by exact prefixLift 3319409
  have htrace : WordTrace (prefixWord ++ tailWord_3319409) baseStart_3319409 baseEnd_3319409 := by
    simpa [prefixWord, tailWord_3319409, baseEnd_3319409] using wordTrace_append hprefix tailTrace_3319409
  have hstable : (prefixWord ++ tailWord_3319409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319409).length < 2 ^ (prefixWord ++ tailWord_3319409).sum := by decide
  have hdescent : baseEnd_3319409 < baseStart_3319409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319432 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 5]
def baseStart_3319432 : Nat := 118140960795 + 3319432 * 2 ^ 59
def prefixEnd_3319432 : Nat := 4983230072969 + 3 ^ 40 * 3319432 * 2
def baseEnd_3319432 : Nat := 378769803536747097940937

theorem tailTrace_3319432 : CollatzResearch.WordTrace tailWord_3319432 prefixEnd_3319432 378769803536747097940937 := by
  unfold tailWord_3319432
  simp only [CollatzResearch.WordTrace]
  refine ⟨60534815655136126348196275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80713087540181501797595033 60534815655136126348196275)
  ·
    refine ⟨90802223482704189522294413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60534815655136126348196275 90802223482704189522294413)
    ·
      refine ⟨34050833806014071070860405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90802223482704189522294413 34050833806014071070860405)
      ·
        refine ⟨3192265669313819162893163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34050833806014071070860405 3192265669313819162893163)
        ·
          refine ⟨4788398503970728744339745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192265669313819162893163 4788398503970728744339745)
          ·
            refine ⟨3591298877978046558254809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4788398503970728744339745 3591298877978046558254809)
            ·
              refine ⟨2693474158483534918691107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3591298877978046558254809 2693474158483534918691107)
              ·
                refine ⟨4040211237725302378036661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693474158483534918691107 4040211237725302378036661)
                ·
                  refine ⟨378769803536747097940937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4040211237725302378036661 378769803536747097940937)
                  ·
                    rfl

theorem cell22_3319432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_3319432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319432 prefixEnd_3319432 := by exact prefixLift 3319432
  have htrace : WordTrace (prefixWord ++ tailWord_3319432) baseStart_3319432 baseEnd_3319432 := by
    simpa [prefixWord, tailWord_3319432, baseEnd_3319432] using wordTrace_append hprefix tailTrace_3319432
  have hstable : (prefixWord ++ tailWord_3319432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319432).length < 2 ^ (prefixWord ++ tailWord_3319432).sum := by decide
  have hdescent : baseEnd_3319432 < baseStart_3319432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319441 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 6, 3]
def baseStart_3319441 : Nat := 118140960795 + 3319441 * 2 ^ 59
def prefixEnd_3319441 : Nat := 4983230072969 + 3 ^ 40 * 3319441 * 2
def baseEnd_3319441 : Nat := 1136312491494168270347783

theorem tailTrace_3319441 : CollatzResearch.WordTrace tailWord_3319441 prefixEnd_3319441 1136312491494168270347783 := by
  unfold tailWord_3319441
  simp only [CollatzResearch.WordTrace]
  refine ⟨121069959567239647233470177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80713306378159764822313451 121069959567239647233470177)
  ·
    refine ⟨90802469675429735425102633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121069959567239647233470177 90802469675429735425102633)
    ·
      refine ⟨68101852256572301568826975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90802469675429735425102633 68101852256572301568826975)
      ·
        refine ⟨102152778384858452353240463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68101852256572301568826975 102152778384858452353240463)
        ·
          refine ⟨153229167577287678529860695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102152778384858452353240463 153229167577287678529860695)
          ·
            refine ⟨229843751365931517794791043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153229167577287678529860695 229843751365931517794791043)
            ·
              refine ⟨344765627048897276692186565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229843751365931517794791043 344765627048897276692186565)
              ·
                refine ⟨64643555071668239379784981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344765627048897276692186565 64643555071668239379784981)
                ·
                  refine ⟨3030166643984448720927421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64643555071668239379784981 3030166643984448720927421)
                  ·
                    refine ⟨1136312491494168270347783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030166643984448720927421 1136312491494168270347783)
                    ·
                      rfl

theorem cell22_3319441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_3319441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319441 prefixEnd_3319441 := by exact prefixLift 3319441
  have htrace : WordTrace (prefixWord ++ tailWord_3319441) baseStart_3319441 baseEnd_3319441 := by
    simpa [prefixWord, tailWord_3319441, baseEnd_3319441] using wordTrace_append hprefix tailTrace_3319441
  have hstable : (prefixWord ++ tailWord_3319441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319441).length < 2 ^ (prefixWord ++ tailWord_3319441).sum := by decide
  have hdescent : baseEnd_3319441 < baseStart_3319441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319520 : List Nat := [2, 1, 1, 3, 1, 2, 3, 5, 1, 3]
def baseStart_3319520 : Nat := 118140960795 + 3319520 * 2 ^ 59
def prefixEnd_3319520 : Nat := 4983230072969 + 3 ^ 40 * 3319520 * 2
def baseEnd_3319520 : Nat := 1136339534808638397622541

theorem tailTrace_3319520 : CollatzResearch.WordTrace tailWord_3319520 prefixEnd_3319520 1136339534808638397622541 := by
  unfold tailWord_3319520
  simp only [CollatzResearch.WordTrace]
  refine ⟨60536420466976721862798007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80715227289302295817064009 60536420466976721862798007)
  ·
    refine ⟨90804630700465082794197011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60536420466976721862798007 90804630700465082794197011)
    ·
      refine ⟨136206946050697624191295517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90804630700465082794197011 136206946050697624191295517)
      ·
        refine ⟨51077604769011609071735819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136206946050697624191295517 51077604769011609071735819)
        ·
          refine ⟨76616407153517413607603729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51077604769011609071735819 76616407153517413607603729)
          ·
            refine ⟨57462305365138060205702797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76616407153517413607603729 57462305365138060205702797)
            ·
              refine ⟨21548364511926772577138549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57462305365138060205702797 21548364511926772577138549)
              ·
                refine ⟨2020159172993134929106739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21548364511926772577138549 2020159172993134929106739)
                ·
                  refine ⟨3030238759489702393660109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020159172993134929106739 3030238759489702393660109)
                  ·
                    refine ⟨1136339534808638397622541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030238759489702393660109 1136339534808638397622541)
                    ·
                      rfl

theorem cell22_3319520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 3].length) (baseStart_3319520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319520 prefixEnd_3319520 := by exact prefixLift 3319520
  have htrace : WordTrace (prefixWord ++ tailWord_3319520) baseStart_3319520 baseEnd_3319520 := by
    simpa [prefixWord, tailWord_3319520, baseEnd_3319520] using wordTrace_append hprefix tailTrace_3319520
  have hstable : (prefixWord ++ tailWord_3319520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319520).length < 2 ^ (prefixWord ++ tailWord_3319520).sum := by decide
  have hdescent : baseEnd_3319520 < baseStart_3319520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319531 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 2, 5]
def baseStart_3319531 : Nat := 118140960795 + 3319531 * 2 ^ 59
def prefixEnd_3319531 : Nat := 4983230072969 + 3 ^ 40 * 3319531 * 2
def baseEnd_3319531 : Nat := 1136343300333438035597507

theorem tailTrace_3319531 : CollatzResearch.WordTrace tailWord_3319531 prefixEnd_3319531 1136343300333438035597507 := by
  unfold tailWord_3319531
  simp only [CollatzResearch.WordTrace]
  refine ⟨121073242136913592604246447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80715494757942395069497631 121073242136913592604246447)
  ·
    refine ⟨181609863205370388906369671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121073242136913592604246447 181609863205370388906369671)
    ·
      refine ⟨272414794808055583359554507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181609863205370388906369671 272414794808055583359554507)
      ·
        refine ⟨408622192212083375039331761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272414794808055583359554507 408622192212083375039331761)
        ·
          refine ⟨306466644159062531279498821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408622192212083375039331761 306466644159062531279498821)
          ·
            refine ⟨57462495779824224614906029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306466644159062531279498821 57462495779824224614906029)
            ·
              refine ⟨21548435917434084230589761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57462495779824224614906029 21548435917434084230589761)
              ·
                refine ⟨16161326938075563172942321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21548435917434084230589761 16161326938075563172942321)
                ·
                  refine ⟨12120995203556672379706741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16161326938075563172942321 12120995203556672379706741)
                  ·
                    refine ⟨1136343300333438035597507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12120995203556672379706741 1136343300333438035597507)
                    ·
                      rfl

theorem cell22_3319531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_3319531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319531 prefixEnd_3319531 := by exact prefixLift 3319531
  have htrace : WordTrace (prefixWord ++ tailWord_3319531) baseStart_3319531 baseEnd_3319531 := by
    simpa [prefixWord, tailWord_3319531, baseEnd_3319531] using wordTrace_append hprefix tailTrace_3319531
  have hstable : (prefixWord ++ tailWord_3319531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319531).length < 2 ^ (prefixWord ++ tailWord_3319531).sum := by decide
  have hdescent : baseEnd_3319531 < baseStart_3319531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319533 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3319533 : Nat := 118140960795 + 3319533 * 2 ^ 59
def prefixEnd_3319533 : Nat := 4983230072969 + 3 ^ 40 * 3319533 * 2
def baseEnd_3319533 : Nat := 378781328324770232349167

theorem tailTrace_3319533 : CollatzResearch.WordTrace tailWord_3319533 prefixEnd_3319533 378781328324770232349167 := by
  unfold tailWord_3319533
  simp only [CollatzResearch.WordTrace]
  refine ⟨121073315082906346945819253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80715543388604231297212835 121073315082906346945819253)
  ·
    refine ⟨11350623289022470026170555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121073315082906346945819253 11350623289022470026170555)
    ·
      refine ⟨17025934933533705039255833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11350623289022470026170555 17025934933533705039255833)
      ·
        refine ⟨12769451200150278779441875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17025934933533705039255833 12769451200150278779441875)
        ·
          refine ⟨19154176800225418169162813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12769451200150278779441875 19154176800225418169162813)
          ·
            refine ⟨7182816300084531813436055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19154176800225418169162813 7182816300084531813436055)
            ·
              refine ⟨10774224450126797720154083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182816300084531813436055 10774224450126797720154083)
              ·
                refine ⟨16161336675190196580231125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10774224450126797720154083 16161336675190196580231125)
                ·
                  refine ⟨378781328324770232349167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16161336675190196580231125 378781328324770232349167)
                  ·
                    rfl

theorem cell22_3319533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3319533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319533 prefixEnd_3319533 := by exact prefixLift 3319533
  have htrace : WordTrace (prefixWord ++ tailWord_3319533) baseStart_3319533 baseEnd_3319533 := by
    simpa [prefixWord, tailWord_3319533, baseEnd_3319533] using wordTrace_append hprefix tailTrace_3319533
  have hstable : (prefixWord ++ tailWord_3319533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319533).length < 2 ^ (prefixWord ++ tailWord_3319533).sum := by decide
  have hdescent : baseEnd_3319533 < baseStart_3319533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319563 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 1, 4]
def baseStart_3319563 : Nat := 118140960795 + 3319563 * 2 ^ 59
def prefixEnd_3319563 : Nat := 4983230072969 + 3 ^ 40 * 3319563 * 2
def baseEnd_3319563 : Nat := 1136354254587400618797409

theorem tailTrace_3319563 : CollatzResearch.WordTrace tailWord_3319563 prefixEnd_3319563 1136354254587400618797409 := by
  unfold tailWord_3319563
  simp only [CollatzResearch.WordTrace]
  refine ⟨121074409272797662069411343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80716272848531774712940895 121074409272797662069411343)
  ·
    refine ⟨181611613909196493104117015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121074409272797662069411343 181611613909196493104117015)
    ·
      refine ⟨272417420863794739656175523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181611613909196493104117015 272417420863794739656175523)
      ·
        refine ⟨408626131295692109484263285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272417420863794739656175523 408626131295692109484263285)
        ·
          refine ⟨38308699808971135264149683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 408626131295692109484263285 38308699808971135264149683)
          ·
            refine ⟨57463049713456702896224525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38308699808971135264149683 57463049713456702896224525)
            ·
              refine ⟨21548643642546263586084197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57463049713456702896224525 21548643642546263586084197)
              ·
                refine ⟨4040370682977424422390787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21548643642546263586084197 4040370682977424422390787)
                ·
                  refine ⟨6060556024466136633586181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040370682977424422390787 6060556024466136633586181)
                  ·
                    refine ⟨1136354254587400618797409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6060556024466136633586181 1136354254587400618797409)
                    ·
                      rfl

theorem cell22_3319563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 4].length) (baseStart_3319563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319563 prefixEnd_3319563 := by exact prefixLift 3319563
  have htrace : WordTrace (prefixWord ++ tailWord_3319563) baseStart_3319563 baseEnd_3319563 := by
    simpa [prefixWord, tailWord_3319563, baseEnd_3319563] using wordTrace_append hprefix tailTrace_3319563
  have hstable : (prefixWord ++ tailWord_3319563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319563).length < 2 ^ (prefixWord ++ tailWord_3319563).sum := by decide
  have hdescent : baseEnd_3319563 < baseStart_3319563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319644 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3319644 : Nat := 118140960795 + 3319644 * 2 ^ 59
def prefixEnd_3319644 : Nat := 4983230072969 + 3 ^ 40 * 3319644 * 2
def baseEnd_3319644 : Nat := 1136381982542743407522161

theorem tailTrace_3319644 : CollatzResearch.WordTrace tailWord_3319644 prefixEnd_3319644 1136381982542743407522161 := by
  unfold tailWord_3319644
  simp only [CollatzResearch.WordTrace]
  refine ⟨60538681792752106451554993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80718242390336141935406657 60538681792752106451554993)
  ·
    refine ⟨45404011344564079838666245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60538681792752106451554993 45404011344564079838666245)
    ·
      refine ⟨8513252127105764969749921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45404011344564079838666245 8513252127105764969749921)
      ·
        refine ⟨6384939095329323727312441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8513252127105764969749921 6384939095329323727312441)
        ·
          refine ⟨4788704321496992795484331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6384939095329323727312441 4788704321496992795484331)
          ·
            refine ⟨7183056482245489193226497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788704321496992795484331 7183056482245489193226497)
            ·
              refine ⟨5387292361684116894919873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183056482245489193226497 5387292361684116894919873)
              ·
                refine ⟨4040469271263087671189905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5387292361684116894919873 4040469271263087671189905)
                ·
                  refine ⟨3030351953447315753392429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040469271263087671189905 3030351953447315753392429)
                  ·
                    refine ⟨1136381982542743407522161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030351953447315753392429 1136381982542743407522161)
                    ·
                      rfl

theorem cell22_3319644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3319644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319644 prefixEnd_3319644 := by exact prefixLift 3319644
  have htrace : WordTrace (prefixWord ++ tailWord_3319644) baseStart_3319644 baseEnd_3319644 := by
    simpa [prefixWord, tailWord_3319644, baseEnd_3319644] using wordTrace_append hprefix tailTrace_3319644
  have hstable : (prefixWord ++ tailWord_3319644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319644).length < 2 ^ (prefixWord ++ tailWord_3319644).sum := by decide
  have hdescent : baseEnd_3319644 < baseStart_3319644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319655 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3319655 : Nat := 118140960795 + 3319655 * 2 ^ 59
def prefixEnd_3319655 : Nat := 4983230072969 + 3 ^ 40 * 3319655 * 2
def baseEnd_3319655 : Nat := 1136385748067543045497127

theorem tailTrace_3319655 : CollatzResearch.WordTrace tailWord_3319655 prefixEnd_3319655 1136385748067543045497127 := by
  unfold tailWord_3319655
  simp only [CollatzResearch.WordTrace]
  refine ⟨121077764788464361781760419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80718509858976241187840279 121077764788464361781760419)
  ·
    refine ⟨181616647182696542672640629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121077764788464361781760419 181616647182696542672640629)
    ·
      refine ⟨17026560673377800875560059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181616647182696542672640629 17026560673377800875560059)
      ·
        refine ⟨25539841010066701313340089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17026560673377800875560059 25539841010066701313340089)
        ·
          refine ⟨19154880757550025985005067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25539841010066701313340089 19154880757550025985005067)
          ·
            refine ⟨28732321136325038977507601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19154880757550025985005067 28732321136325038977507601)
            ·
              refine ⟨21549240852243779233130701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28732321136325038977507601 21549240852243779233130701)
              ·
                refine ⟨8080965319591417212424013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21549240852243779233130701 8080965319591417212424013)
                ·
                  refine ⟨3030361994846781454659005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8080965319591417212424013 3030361994846781454659005)
                  ·
                    refine ⟨1136385748067543045497127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030361994846781454659005 1136385748067543045497127)
                    ·
                      rfl

theorem cell22_3319655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3319655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319655 prefixEnd_3319655 := by exact prefixLift 3319655
  have htrace : WordTrace (prefixWord ++ tailWord_3319655) baseStart_3319655 baseEnd_3319655 := by
    simpa [prefixWord, tailWord_3319655, baseEnd_3319655] using wordTrace_append hprefix tailTrace_3319655
  have hstable : (prefixWord ++ tailWord_3319655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319655).length < 2 ^ (prefixWord ++ tailWord_3319655).sum := by decide
  have hdescent : baseEnd_3319655 < baseStart_3319655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319700 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3319700 : Nat := 118140960795 + 3319700 * 2 ^ 59
def prefixEnd_3319700 : Nat := 4983230072969 + 3 ^ 40 * 3319700 * 2
def baseEnd_3319700 : Nat := 1136401152487177928121989

theorem tailTrace_3319700 : CollatzResearch.WordTrace tailWord_3319700 prefixEnd_3319700 1136401152487177928121989 := by
  unfold tailWord_3319700
  simp only [CollatzResearch.WordTrace]
  refine ⟨60539703036650667233574277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80719604048867556311432369 60539703036650667233574277)
  ·
    refine ⟨11351194319372000106295177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60539703036650667233574277 11351194319372000106295177)
    ·
      refine ⟨8513395739529000079721383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11351194319372000106295177 8513395739529000079721383)
      ·
        refine ⟨12770093609293500119582075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8513395739529000079721383 12770093609293500119582075)
        ·
          refine ⟨19155140413940250179373113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12770093609293500119582075 19155140413940250179373113)
          ·
            refine ⟨14366355310455187634529835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19155140413940250179373113 14366355310455187634529835)
            ·
              refine ⟨21549532965682781451794753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14366355310455187634529835 21549532965682781451794753)
              ·
                refine ⟨16162149724262086088846065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21549532965682781451794753 16162149724262086088846065)
                ·
                  refine ⟨12121612293196564566634549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16162149724262086088846065 12121612293196564566634549)
                  ·
                    refine ⟨1136401152487177928121989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12121612293196564566634549 1136401152487177928121989)
                    ·
                      rfl

theorem cell22_3319700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3319700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319700 prefixEnd_3319700 := by exact prefixLift 3319700
  have htrace : WordTrace (prefixWord ++ tailWord_3319700) baseStart_3319700 baseEnd_3319700 := by
    simpa [prefixWord, tailWord_3319700, baseEnd_3319700] using wordTrace_append hprefix tailTrace_3319700
  have hstable : (prefixWord ++ tailWord_3319700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319700).length < 2 ^ (prefixWord ++ tailWord_3319700).sum := by decide
  have hdescent : baseEnd_3319700 < baseStart_3319700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319743 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 1, 6]
def baseStart_3319743 : Nat := 118140960795 + 3319743 * 2 ^ 59
def prefixEnd_3319743 : Nat := 4983230072969 + 3 ^ 40 * 3319743 * 2
def baseEnd_3319743 : Nat := 1136415872265940149296857

theorem tailTrace_3319743 : CollatzResearch.WordTrace tailWord_3319743 prefixEnd_3319743 1136415872265940149296857 := by
  unfold tailWord_3319743
  simp only [CollatzResearch.WordTrace]
  refine ⟨121080974412145552810963883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80720649608097035207309255 121080974412145552810963883)
  ·
    refine ⟨181621461618218329216445825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121080974412145552810963883 181621461618218329216445825)
    ·
      refine ⟨136216096213663746912334369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181621461618218329216445825 136216096213663746912334369)
      ·
        refine ⟨102162072160247810184250777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136216096213663746912334369 102162072160247810184250777)
        ·
          refine ⟨76621554120185857638188083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102162072160247810184250777 76621554120185857638188083)
          ·
            refine ⟨114932331180278786457282125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76621554120185857638188083 114932331180278786457282125)
            ·
              refine ⟨43099624192604544921480797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114932331180278786457282125 43099624192604544921480797)
              ·
                refine ⟨16162359072226704345555299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43099624192604544921480797 16162359072226704345555299)
                ·
                  refine ⟨24243538608340056518332949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16162359072226704345555299 24243538608340056518332949)
                  ·
                    refine ⟨1136415872265940149296857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24243538608340056518332949 1136415872265940149296857)
                    ·
                      rfl

theorem cell22_3319743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_3319743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319743 prefixEnd_3319743 := by exact prefixLift 3319743
  have htrace : WordTrace (prefixWord ++ tailWord_3319743) baseStart_3319743 baseEnd_3319743 := by
    simpa [prefixWord, tailWord_3319743, baseEnd_3319743] using wordTrace_append hprefix tailTrace_3319743
  have hstable : (prefixWord ++ tailWord_3319743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319743).length < 2 ^ (prefixWord ++ tailWord_3319743).sum := by decide
  have hdescent : baseEnd_3319743 < baseStart_3319743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319764 : List Nat := [2, 4, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3319764 : Nat := 118140960795 + 3319764 * 2 ^ 59
def prefixEnd_3319764 : Nat := 4983230072969 + 3 ^ 40 * 3319764 * 2
def baseEnd_3319764 : Nat := 378807686998367698173931

theorem tailTrace_3319764 : CollatzResearch.WordTrace tailWord_3319764 prefixEnd_3319764 378807686998367698173931 := by
  unfold tailWord_3319764
  simp only [CollatzResearch.WordTrace]
  refine ⟨60540870172534736698739173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80721160230046315598318897 60540870172534736698739173)
  ·
    refine ⟨11351413157350263131013595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60540870172534736698739173 11351413157350263131013595)
    ·
      refine ⟨17027119736025394696520393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11351413157350263131013595 17027119736025394696520393)
      ·
        refine ⟨12770339802019046022390295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17027119736025394696520393 12770339802019046022390295)
        ·
          refine ⟨19155509703028569033585443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12770339802019046022390295 19155509703028569033585443)
          ·
            refine ⟨28733264554542853550378165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19155509703028569033585443 28733264554542853550378165)
            ·
              refine ⟨2693743551988392520347953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28733264554542853550378165 2693743551988392520347953)
              ·
                refine ⟨2020307663991294390260965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2693743551988392520347953 2020307663991294390260965)
                ·
                  refine ⟨378807686998367698173931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2020307663991294390260965 378807686998367698173931)
                  ·
                    rfl

theorem cell22_3319764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3319764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319764 prefixEnd_3319764 := by exact prefixLift 3319764
  have htrace : WordTrace (prefixWord ++ tailWord_3319764) baseStart_3319764 baseEnd_3319764 := by
    simpa [prefixWord, tailWord_3319764, baseEnd_3319764] using wordTrace_append hprefix tailTrace_3319764
  have hstable : (prefixWord ++ tailWord_3319764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319764).length < 2 ^ (prefixWord ++ tailWord_3319764).sum := by decide
  have hdescent : baseEnd_3319764 < baseStart_3319764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319775 : List Nat := [1, 1, 2, 3, 4, 2, 2, 7]
def baseStart_3319775 : Nat := 118140960795 + 3319775 * 2 ^ 59
def prefixEnd_3319775 : Nat := 4983230072969 + 3 ^ 40 * 3319775 * 2
def baseEnd_3319775 : Nat := 126269647391100303610751

theorem tailTrace_3319775 : CollatzResearch.WordTrace tailWord_3319775 prefixEnd_3319775 126269647391100303610751 := by
  unfold tailWord_3319775
  simp only [CollatzResearch.WordTrace]
  refine ⟨121082141548029622276128779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80721427698686414850752519 121082141548029622276128779)
  ·
    refine ⟨181623212322044433414193169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121082141548029622276128779 181623212322044433414193169)
    ·
      refine ⟨136217409241533325060644877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181623212322044433414193169 136217409241533325060644877)
      ·
        refine ⟨51081528465574996897741829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136217409241533325060644877 51081528465574996897741829)
        ·
          refine ⟨9577786587295311918326593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51081528465574996897741829 9577786587295311918326593)
          ·
            refine ⟨7183339940471483938744945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9577786587295311918326593 7183339940471483938744945)
            ·
              refine ⟨5387504955353612954058709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183339940471483938744945 5387504955353612954058709)
              ·
                refine ⟨126269647391100303610751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5387504955353612954058709 126269647391100303610751)
                ·
                  rfl

theorem cell22_3319775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 7].length) (baseStart_3319775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319775 prefixEnd_3319775 := by exact prefixLift 3319775
  have htrace : WordTrace (prefixWord ++ tailWord_3319775) baseStart_3319775 baseEnd_3319775 := by
    simpa [prefixWord, tailWord_3319775, baseEnd_3319775] using wordTrace_append hprefix tailTrace_3319775
  have hstable : (prefixWord ++ tailWord_3319775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319775).length < 2 ^ (prefixWord ++ tailWord_3319775).sum := by decide
  have hdescent : baseEnd_3319775 < baseStart_3319775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319779 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 2, 3]
def baseStart_3319779 : Nat := 118140960795 + 3319779 * 2 ^ 59
def prefixEnd_3319779 : Nat := 4983230072969 + 3 ^ 40 * 3319779 * 2
def baseEnd_3319779 : Nat := 1136428195801648055396747

theorem tailTrace_3319779 : CollatzResearch.WordTrace tailWord_3319779 prefixEnd_3319779 1136428195801648055396747 := by
  unfold tailWord_3319779
  simp only [CollatzResearch.WordTrace]
  refine ⟨121082287440015130959274391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80721524960010087306182927 121082287440015130959274391)
  ·
    refine ⟨181623431160022696438911587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121082287440015130959274391 181623431160022696438911587)
    ·
      refine ⟨272435146740034044658367381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181623431160022696438911587 272435146740034044658367381)
      ·
        refine ⟨12770397503439095843360971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272435146740034044658367381 12770397503439095843360971)
        ·
          refine ⟨19155596255158643765041457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12770397503439095843360971 19155596255158643765041457)
          ·
            refine ⟨14366697191368982823781093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19155596255158643765041457 14366697191368982823781093)
            ·
              refine ⟨2693755723381684279458955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14366697191368982823781093 2693755723381684279458955)
              ·
                refine ⟨4040633585072526419188433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693755723381684279458955 4040633585072526419188433)
                ·
                  refine ⟨3030475188804394814391325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040633585072526419188433 3030475188804394814391325)
                  ·
                    refine ⟨1136428195801648055396747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030475188804394814391325 1136428195801648055396747)
                    ·
                      rfl

theorem cell22_3319779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 3].length) (baseStart_3319779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319779 prefixEnd_3319779 := by exact prefixLift 3319779
  have htrace : WordTrace (prefixWord ++ tailWord_3319779) baseStart_3319779 baseEnd_3319779 := by
    simpa [prefixWord, tailWord_3319779, baseEnd_3319779] using wordTrace_append hprefix tailTrace_3319779
  have hstable : (prefixWord ++ tailWord_3319779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319779).length < 2 ^ (prefixWord ++ tailWord_3319779).sum := by decide
  have hdescent : baseEnd_3319779 < baseStart_3319779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319803 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 9]
def baseStart_3319803 : Nat := 118140960795 + 3319803 * 2 ^ 59
def prefixEnd_3319803 : Nat := 4983230072969 + 3 ^ 40 * 3319803 * 2
def baseEnd_3319803 : Nat := 378812137164039997598891

theorem tailTrace_3319803 : CollatzResearch.WordTrace tailWord_3319803 prefixEnd_3319803 378812137164039997598891 := by
  unfold tailWord_3319803
  simp only [CollatzResearch.WordTrace]
  refine ⟨121083162791928183058148063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80722108527952122038765375 121083162791928183058148063)
  ·
    refine ⟨181624744187892274587222095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121083162791928183058148063 181624744187892274587222095)
    ·
      refine ⟨272437116281838411880833143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181624744187892274587222095 272437116281838411880833143)
      ·
        refine ⟨408655674422757617821249715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272437116281838411880833143 408655674422757617821249715)
        ·
          refine ⟨612983511634136426731874573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408655674422757617821249715 612983511634136426731874573)
          ·
            refine ⟨229868816862801160024452965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612983511634136426731874573 229868816862801160024452965)
            ·
              refine ⟨43100403161775217504584931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229868816862801160024452965 43100403161775217504584931)
              ·
                refine ⟨64650604742662826256877397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43100403161775217504584931 64650604742662826256877397)
                ·
                  refine ⟨378812137164039997598891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64650604742662826256877397 378812137164039997598891)
                  ·
                    rfl

theorem cell22_3319803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_3319803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319803 prefixEnd_3319803 := by exact prefixLift 3319803
  have htrace : WordTrace (prefixWord ++ tailWord_3319803) baseStart_3319803 baseEnd_3319803 := by
    simpa [prefixWord, tailWord_3319803, baseEnd_3319803] using wordTrace_append hprefix tailTrace_3319803
  have hstable : (prefixWord ++ tailWord_3319803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319803).length < 2 ^ (prefixWord ++ tailWord_3319803).sum := by decide
  have hdescent : baseEnd_3319803 < baseStart_3319803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319837 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 5]
def baseStart_3319837 : Nat := 118140960795 + 3319837 * 2 ^ 59
def prefixEnd_3319837 : Nat := 4983230072969 + 3 ^ 40 * 3319837 * 2
def baseEnd_3319837 : Nat := 378816016795651745815523

theorem tailTrace_3319837 : CollatzResearch.WordTrace tailWord_3319837 prefixEnd_3319837 378816016795651745815523 := by
  unfold tailWord_3319837
  simp only [CollatzResearch.WordTrace]
  refine ⟨121084402873805006864885765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80722935249203337909923843 121084402873805006864885765)
  ·
    refine ⟨22703325538838438787166081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121084402873805006864885765 22703325538838438787166081)
    ·
      refine ⟨17027494154128829090374561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22703325538838438787166081 17027494154128829090374561)
      ·
        refine ⟨12770620615596621817780921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17027494154128829090374561 12770620615596621817780921)
        ·
          refine ⟨9577965461697466363335691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12770620615596621817780921 9577965461697466363335691)
          ·
            refine ⟨14366948192546199545003537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9577965461697466363335691 14366948192546199545003537)
            ·
              refine ⟨10775211144409649658752653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14366948192546199545003537 10775211144409649658752653)
              ·
                refine ⟨4040704179153618622032245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10775211144409649658752653 4040704179153618622032245)
                ·
                  refine ⟨378816016795651745815523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4040704179153618622032245 378816016795651745815523)
                  ·
                    rfl

theorem cell22_3319837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_3319837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319837 prefixEnd_3319837 := by exact prefixLift 3319837
  have htrace : WordTrace (prefixWord ++ tailWord_3319837) baseStart_3319837 baseEnd_3319837 := by
    simpa [prefixWord, tailWord_3319837, baseEnd_3319837] using wordTrace_append hprefix tailTrace_3319837
  have hstable : (prefixWord ++ tailWord_3319837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319837).length < 2 ^ (prefixWord ++ tailWord_3319837).sum := by decide
  have hdescent : baseEnd_3319837 < baseStart_3319837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319895 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 1, 6]
def baseStart_3319895 : Nat := 118140960795 + 3319895 * 2 ^ 59
def prefixEnd_3319895 : Nat := 4983230072969 + 3 ^ 40 * 3319895 * 2
def baseEnd_3319895 : Nat := 1136467904972262419496391

theorem tailTrace_3319895 : CollatzResearch.WordTrace tailWord_3319895 prefixEnd_3319895 1136467904972262419496391 := by
  unfold tailWord_3319895
  simp only [CollatzResearch.WordTrace]
  refine ⟨121086518307594882770497139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80724345538396588513664759 121086518307594882770497139)
  ·
    refine ⟨181629777461392324155745709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121086518307594882770497139 181629777461392324155745709)
    ·
      refine ⟨68111166548022121558404641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181629777461392324155745709 68111166548022121558404641)
      ·
        refine ⟨51083374911016591168803481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68111166548022121558404641 51083374911016591168803481)
        ·
          refine ⟨38312531183262443376602611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51083374911016591168803481 38312531183262443376602611)
          ·
            refine ⟨57468796774893665064903917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38312531183262443376602611 57468796774893665064903917)
            ·
              refine ⟨21550798790585124399338969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57468796774893665064903917 21550798790585124399338969)
              ·
                refine ⟨16163099092938843299504227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21550798790585124399338969 16163099092938843299504227)
                ·
                  refine ⟨24244648639408264949256341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16163099092938843299504227 24244648639408264949256341)
                  ·
                    refine ⟨1136467904972262419496391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24244648639408264949256341 1136467904972262419496391)
                    ·
                      rfl

theorem cell22_3319895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_3319895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319895 prefixEnd_3319895 := by exact prefixLift 3319895
  have htrace : WordTrace (prefixWord ++ tailWord_3319895) baseStart_3319895 baseEnd_3319895 := by
    simpa [prefixWord, tailWord_3319895, baseEnd_3319895] using wordTrace_append hprefix tailTrace_3319895
  have hstable : (prefixWord ++ tailWord_3319895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319895).length < 2 ^ (prefixWord ++ tailWord_3319895).sum := by decide
  have hdescent : baseEnd_3319895 < baseStart_3319895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319901 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3319901 : Nat := 118140960795 + 3319901 * 2 ^ 59
def prefixEnd_3319901 : Nat := 4983230072969 + 3 ^ 40 * 3319901 * 2
def baseEnd_3319901 : Nat := 1136469958894880403846373

theorem tailTrace_3319901 : CollatzResearch.WordTrace tailWord_3319901 prefixEnd_3319901 1136469958894880403846373 := by
  unfold tailWord_3319901
  simp only [CollatzResearch.WordTrace]
  refine ⟨121086737145573145795215557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80724491430382097196810371 121086737145573145795215557)
  ·
    refine ⟨22703763214794964836602917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121086737145573145795215557 22703763214794964836602917)
    ·
      refine ⟨4256955602774055906863047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22703763214794964836602917 4256955602774055906863047)
      ·
        refine ⟨6385433404161083860294571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4256955602774055906863047 6385433404161083860294571)
        ·
          refine ⟨9578150106241625790441857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6385433404161083860294571 9578150106241625790441857)
          ·
            refine ⟨7183612579681219342831393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9578150106241625790441857 7183612579681219342831393)
            ·
              refine ⟨5387709434760914507123545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183612579681219342831393 5387709434760914507123545)
              ·
                refine ⟨4040782076070685880342659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5387709434760914507123545 4040782076070685880342659)
                ·
                  refine ⟨6061173114106028820513989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040782076070685880342659 6061173114106028820513989)
                  ·
                    refine ⟨1136469958894880403846373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6061173114106028820513989 1136469958894880403846373)
                    ·
                      rfl

theorem cell22_3319901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3319901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3319901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3319901 prefixEnd_3319901 := by exact prefixLift 3319901
  have htrace : WordTrace (prefixWord ++ tailWord_3319901) baseStart_3319901 baseEnd_3319901 := by
    simpa [prefixWord, tailWord_3319901, baseEnd_3319901] using wordTrace_append hprefix tailTrace_3319901
  have hstable : (prefixWord ++ tailWord_3319901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319901).length < 2 ^ (prefixWord ++ tailWord_3319901).sum := by decide
  have hdescent : baseEnd_3319901 < baseStart_3319901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320004 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3320004 : Nat := 118140960795 + 3320004 * 2 ^ 59
def prefixEnd_3320004 : Nat := 4983230072969 + 3 ^ 40 * 3320004 * 2
def baseEnd_3320004 : Nat := 1136505217899822468521057

theorem tailTrace_3320004 : CollatzResearch.WordTrace tailWord_3320004 prefixEnd_3320004 1136505217899822468521057 := by
  unfold tailWord_3320004
  simp only [CollatzResearch.WordTrace]
  refine ⟨60545246932099997193107533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80726995909466662924143377 60545246932099997193107533)
  ·
    refine ⟨22704467599537498947415325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60545246932099997193107533 22704467599537498947415325)
    ·
      refine ⟨8514175349826562105280747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22704467599537498947415325 8514175349826562105280747)
      ·
        refine ⟨12771263024739843157921121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514175349826562105280747 12771263024739843157921121)
        ·
          refine ⟨9578447268554882368440841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12771263024739843157921121 9578447268554882368440841)
          ·
            refine ⟨7183835451416161776330631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9578447268554882368440841 7183835451416161776330631)
            ·
              refine ⟨10775753177124242664495947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7183835451416161776330631 10775753177124242664495947)
              ·
                refine ⟨16163629765686363996743921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10775753177124242664495947 16163629765686363996743921)
                ·
                  refine ⟨12122722324264772997557941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16163629765686363996743921 12122722324264772997557941)
                  ·
                    refine ⟨1136505217899822468521057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12122722324264772997557941 1136505217899822468521057)
                    ·
                      rfl

theorem cell22_3320004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3320004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320004 prefixEnd_3320004 := by exact prefixLift 3320004
  have htrace : WordTrace (prefixWord ++ tailWord_3320004) baseStart_3320004 baseEnd_3320004 := by
    simpa [prefixWord, tailWord_3320004, baseEnd_3320004] using wordTrace_append hprefix tailTrace_3320004
  have hstable : (prefixWord ++ tailWord_3320004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320004).length < 2 ^ (prefixWord ++ tailWord_3320004).sum := by decide
  have hdescent : baseEnd_3320004 < baseStart_3320004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320032 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_3320032 : Nat := 118140960795 + 3320032 * 2 ^ 59
def prefixEnd_3320032 : Nat := 4983230072969 + 3 ^ 40 * 3320032 * 2
def baseEnd_3320032 : Nat := 1136514802872039728820971

theorem tailTrace_3320032 : CollatzResearch.WordTrace tailWord_3320032 prefixEnd_3320032 1136514802872039728820971 := by
  unfold tailWord_3320032
  simp only [CollatzResearch.WordTrace]
  refine ⟨60545757554049277584117175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80727676738732370112156233 60545757554049277584117175)
  ·
    refine ⟨90818636331073916376175763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60545757554049277584117175 90818636331073916376175763)
    ·
      refine ⟨136227954496610874564263645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90818636331073916376175763 136227954496610874564263645)
      ·
        refine ⟨51085482936229077961598867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136227954496610874564263645 51085482936229077961598867)
        ·
          refine ⟨76628224404343616942398301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51085482936229077961598867 76628224404343616942398301)
          ·
            refine ⟨28735584151628856353399363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76628224404343616942398301 28735584151628856353399363)
            ·
              refine ⟨43103376227443284530099045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28735584151628856353399363 43103376227443284530099045)
              ·
                refine ⟨8081883042645615849393571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43103376227443284530099045 8081883042645615849393571)
                ·
                  refine ⟨12122824563968423774090357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8081883042645615849393571 12122824563968423774090357)
                  ·
                    refine ⟨1136514802872039728820971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12122824563968423774090357 1136514802872039728820971)
                    ·
                      rfl

theorem cell22_3320032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_3320032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320032 prefixEnd_3320032 := by exact prefixLift 3320032
  have htrace : WordTrace (prefixWord ++ tailWord_3320032) baseStart_3320032 baseEnd_3320032 := by
    simpa [prefixWord, tailWord_3320032, baseEnd_3320032] using wordTrace_append hprefix tailTrace_3320032
  have hstable : (prefixWord ++ tailWord_3320032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320032).length < 2 ^ (prefixWord ++ tailWord_3320032).sum := by decide
  have hdescent : baseEnd_3320032 < baseStart_3320032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320066 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3320066 : Nat := 118140960795 + 3320066 * 2 ^ 59
def prefixEnd_3320066 : Nat := 4983230072969 + 3 ^ 40 * 3320066 * 2
def baseEnd_3320066 : Nat := 1136526441766874973470867

theorem tailTrace_3320066 : CollatzResearch.WordTrace tailWord_3320066 prefixEnd_3320066 1136526441766874973470867 := by
  unfold tailWord_3320066
  simp only [CollatzResearch.WordTrace]
  refine ⟨30273188797493844743743013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80728503459983585983314701 30273188797493844743743013)
  ·
    refine ⟨5676222899530095889451815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30273188797493844743743013 5676222899530095889451815)
    ·
      refine ⟨8514334349295143834177723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676222899530095889451815 8514334349295143834177723)
      ·
        refine ⟨12771501523942715751266585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514334349295143834177723 12771501523942715751266585)
        ·
          refine ⟨9578626142957036813449939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12771501523942715751266585 9578626142957036813449939)
          ·
            refine ⟨14367939214435555220174909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9578626142957036813449939 14367939214435555220174909)
            ·
              refine ⟨5387977205413333207565591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14367939214435555220174909 5387977205413333207565591)
              ·
                refine ⟨8081965808119999811348387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387977205413333207565591 8081965808119999811348387)
                ·
                  refine ⟨12122948712179999717022581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8081965808119999811348387 12122948712179999717022581)
                  ·
                    refine ⟨1136526441766874973470867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12122948712179999717022581 1136526441766874973470867)
                    ·
                      rfl

theorem cell22_3320066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3320066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320066 prefixEnd_3320066 := by exact prefixLift 3320066
  have htrace : WordTrace (prefixWord ++ tailWord_3320066) baseStart_3320066 baseEnd_3320066 := by
    simpa [prefixWord, tailWord_3320066, baseEnd_3320066] using wordTrace_append hprefix tailTrace_3320066
  have hstable : (prefixWord ++ tailWord_3320066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320066).length < 2 ^ (prefixWord ++ tailWord_3320066).sum := by decide
  have hdescent : baseEnd_3320066 < baseStart_3320066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320092 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3320092 : Nat := 118140960795 + 3320092 * 2 ^ 59
def prefixEnd_3320092 : Nat := 4983230072969 + 3 ^ 40 * 3320092 * 2
def baseEnd_3320092 : Nat := 1136535342098219572320787

theorem tailTrace_3320092 : CollatzResearch.WordTrace tailWord_3320092 prefixEnd_3320092 1136535342098219572320787 := by
  unfold tailWord_3320092
  simp only [CollatzResearch.WordTrace]
  refine ⟨60546851743940592707709265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80729135658587456943612353 60546851743940592707709265)
  ·
    refine ⟨45410138807955444530781949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60546851743940592707709265 45410138807955444530781949)
    ·
      refine ⟨17028802052983291699043231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45410138807955444530781949 17028802052983291699043231)
      ·
        refine ⟨25543203079474937548564847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17028802052983291699043231 25543203079474937548564847)
        ·
          refine ⟨38314804619212406322847271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25543203079474937548564847 38314804619212406322847271)
          ·
            refine ⟨57472206928818609484270907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38314804619212406322847271 57472206928818609484270907)
            ·
              refine ⟨86208310393227914226406361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57472206928818609484270907 86208310393227914226406361)
              ·
                refine ⟨64656232794920935669804771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86208310393227914226406361 64656232794920935669804771)
                ·
                  refine ⟨96984349192381403504707157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64656232794920935669804771 96984349192381403504707157)
                  ·
                    refine ⟨1136535342098219572320787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96984349192381403504707157 1136535342098219572320787)
                    ·
                      rfl

theorem cell22_3320092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3320092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320092 prefixEnd_3320092 := by exact prefixLift 3320092
  have htrace : WordTrace (prefixWord ++ tailWord_3320092) baseStart_3320092 baseEnd_3320092 := by
    simpa [prefixWord, tailWord_3320092, baseEnd_3320092] using wordTrace_append hprefix tailTrace_3320092
  have hstable : (prefixWord ++ tailWord_3320092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320092).length < 2 ^ (prefixWord ++ tailWord_3320092).sum := by decide
  have hdescent : baseEnd_3320092 < baseStart_3320092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320111 : List Nat := [1, 1, 2, 1, 2, 1, 4, 6, 1, 3]
def baseStart_3320111 : Nat := 118140960795 + 3320111 * 2 ^ 59
def prefixEnd_3320111 : Nat := 4983230072969 + 3 ^ 40 * 3320111 * 2
def baseEnd_3320111 : Nat := 1136541846186509856095729

theorem tailTrace_3320111 : CollatzResearch.WordTrace tailWord_3320111 prefixEnd_3320111 1136541846186509856095729 := by
  unfold tailWord_3320111
  simp only [CollatzResearch.WordTrace]
  refine ⟨121094396474812351660360187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80729597649874901106906791 121094396474812351660360187)
  ·
    refine ⟨181641594712218527490540281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121094396474812351660360187 181641594712218527490540281)
    ·
      refine ⟨136231196034163895617905211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181641594712218527490540281 136231196034163895617905211)
      ·
        refine ⟨204346794051245843426857817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136231196034163895617905211 204346794051245843426857817)
        ·
          refine ⟨153260095538434382570143363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204346794051245843426857817 153260095538434382570143363)
          ·
            refine ⟨229890143307651573855215045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153260095538434382570143363 229890143307651573855215045)
            ·
              refine ⟨43104401870184670097852821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229890143307651573855215045 43104401870184670097852821)
              ·
                refine ⟨2020518837664906410836851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43104401870184670097852821 2020518837664906410836851)
                ·
                  refine ⟨3030778256497359616255277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020518837664906410836851 3030778256497359616255277)
                  ·
                    refine ⟨1136541846186509856095729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030778256497359616255277 1136541846186509856095729)
                    ·
                      rfl

theorem cell22_3320111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 3].length) (baseStart_3320111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320111 prefixEnd_3320111 := by exact prefixLift 3320111
  have htrace : WordTrace (prefixWord ++ tailWord_3320111) baseStart_3320111 baseEnd_3320111 := by
    simpa [prefixWord, tailWord_3320111, baseEnd_3320111] using wordTrace_append hprefix tailTrace_3320111
  have hstable : (prefixWord ++ tailWord_3320111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320111).length < 2 ^ (prefixWord ++ tailWord_3320111).sum := by decide
  have hdescent : baseEnd_3320111 < baseStart_3320111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320124 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 5]
def baseStart_3320124 : Nat := 118140960795 + 3320124 * 2 ^ 59
def prefixEnd_3320124 : Nat := 4983230072969 + 3 ^ 40 * 3320124 * 2
def baseEnd_3320124 : Nat := 378848765450727385173563

theorem tailTrace_3320124 : CollatzResearch.WordTrace tailWord_3320124 prefixEnd_3320124 378848765450727385173563 := by
  unfold tailWord_3320124
  simp only [CollatzResearch.WordTrace]
  refine ⟨60547435311882627440291713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80729913749176836587055617 60547435311882627440291713)
  ·
    refine ⟨45410576483911970580218785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60547435311882627440291713 45410576483911970580218785)
    ·
      refine ⟨34057932362933977935164089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45410576483911970580218785 34057932362933977935164089)
      ·
        refine ⟨25543449272200483451373067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34057932362933977935164089 25543449272200483451373067)
        ·
          refine ⟨38315173908300725177059601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25543449272200483451373067 38315173908300725177059601)
          ·
            refine ⟨28736380431225543882794701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38315173908300725177059601 28736380431225543882794701)
            ·
              refine ⟨10776142661709578956048013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28736380431225543882794701 10776142661709578956048013)
              ·
                refine ⟨4041053498141092108518005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10776142661709578956048013 4041053498141092108518005)
                ·
                  refine ⟨378848765450727385173563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4041053498141092108518005 378848765450727385173563)
                  ·
                    rfl

theorem cell22_3320124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_3320124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320124 prefixEnd_3320124 := by exact prefixLift 3320124
  have htrace : WordTrace (prefixWord ++ tailWord_3320124) baseStart_3320124 baseEnd_3320124 := by
    simpa [prefixWord, tailWord_3320124, baseEnd_3320124] using wordTrace_append hprefix tailTrace_3320124
  have hstable : (prefixWord ++ tailWord_3320124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320124).length < 2 ^ (prefixWord ++ tailWord_3320124).sum := by decide
  have hdescent : baseEnd_3320124 < baseStart_3320124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320152 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 10]
def baseStart_3320152 : Nat := 118140960795 + 3320152 * 2 ^ 59
def prefixEnd_3320152 : Nat := 4983230072969 + 3 ^ 40 * 3320152 * 2
def baseEnd_3320152 : Nat := 378851960441466471940201

theorem tailTrace_3320152 : CollatzResearch.WordTrace tailWord_3320152 prefixEnd_3320152 378851960441466471940201 := by
  unfold tailWord_3320152
  simp only [CollatzResearch.WordTrace]
  refine ⟨60547945933831907831301355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80730594578442543775068473 60547945933831907831301355)
  ·
    refine ⟨90821918900747861746952033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60547945933831907831301355 90821918900747861746952033)
    ·
      refine ⟨68116439175560896310214025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90821918900747861746952033 68116439175560896310214025)
      ·
        refine ⟨51087329381670672232660519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68116439175560896310214025 51087329381670672232660519)
        ·
          refine ⟨76630994072506008348990779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51087329381670672232660519 76630994072506008348990779)
          ·
            refine ⟨114946491108759012523486169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76630994072506008348990779 114946491108759012523486169)
            ·
              refine ⟨86209868331569259392614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114946491108759012523486169 86209868331569259392614627)
              ·
                refine ⟨129314802497353889088921941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86209868331569259392614627 129314802497353889088921941)
                ·
                  refine ⟨378851960441466471940201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129314802497353889088921941 378851960441466471940201)
                  ·
                    rfl

theorem cell22_3320152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_3320152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320152 prefixEnd_3320152 := by exact prefixLift 3320152
  have htrace : WordTrace (prefixWord ++ tailWord_3320152) baseStart_3320152 baseEnd_3320152 := by
    simpa [prefixWord, tailWord_3320152, baseEnd_3320152] using wordTrace_append hprefix tailTrace_3320152
  have hstable : (prefixWord ++ tailWord_3320152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320152).length < 2 ^ (prefixWord ++ tailWord_3320152).sum := by decide
  have hdescent : baseEnd_3320152 < baseStart_3320152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320162 : List Nat := [3, 3, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3320162 : Nat := 118140960795 + 3320162 * 2 ^ 59
def prefixEnd_3320162 : Nat := 4983230072969 + 3 ^ 40 * 3320162 * 2
def baseEnd_3320162 : Nat := 1136559304528762723070573

theorem tailTrace_3320162 : CollatzResearch.WordTrace tailWord_3320162 prefixEnd_3320162 1136559304528762723070573 := by
  unfold tailWord_3320162
  simp only [CollatzResearch.WordTrace]
  refine ⟨30274064149406896842616685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80730837731751724913644493 30274064149406896842616685)
  ·
    refine ⟨11352774056027586315981257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30274064149406896842616685 11352774056027586315981257)
    ·
      refine ⟨8514580542020689736985943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11352774056027586315981257 8514580542020689736985943)
      ·
        refine ⟨12771870813031034605478915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514580542020689736985943 12771870813031034605478915)
        ·
          refine ⟨19157806219546551908218373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12771870813031034605478915 19157806219546551908218373)
          ·
            refine ⟨3592088666164978482790945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19157806219546551908218373 3592088666164978482790945)
            ·
              refine ⟨2694066499623733862093209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3592088666164978482790945 2694066499623733862093209)
              ·
                refine ⟨2020549874717800396569907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694066499623733862093209 2020549874717800396569907)
                ·
                  refine ⟨3030824812076700594854861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020549874717800396569907 3030824812076700594854861)
                  ·
                    refine ⟨1136559304528762723070573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030824812076700594854861 1136559304528762723070573)
                    ·
                      rfl

theorem cell22_3320162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3320162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320162 prefixEnd_3320162 := by exact prefixLift 3320162
  have htrace : WordTrace (prefixWord ++ tailWord_3320162) baseStart_3320162 baseEnd_3320162 := by
    simpa [prefixWord, tailWord_3320162, baseEnd_3320162] using wordTrace_append hprefix tailTrace_3320162
  have hstable : (prefixWord ++ tailWord_3320162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320162).length < 2 ^ (prefixWord ++ tailWord_3320162).sum := by decide
  have hdescent : baseEnd_3320162 < baseStart_3320162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320199 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3320199 : Nat := 118140960795 + 3320199 * 2 ^ 59
def prefixEnd_3320199 : Nat := 4983230072969 + 3 ^ 40 * 3320199 * 2
def baseEnd_3320199 : Nat := 1136571970384906959895459

theorem tailTrace_3320199 : CollatzResearch.WordTrace tailWord_3320199 prefixEnd_3320199 1136571970384906959895459 := by
  unfold tailWord_3320199
  simp only [CollatzResearch.WordTrace]
  refine ⟨121097606098493542689563651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80731737398995695126375767 121097606098493542689563651)
  ·
    refine ⟨181646409147740314034345477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121097606098493542689563651 181646409147740314034345477)
    ·
      refine ⟨34058701715201308881439777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181646409147740314034345477 34058701715201308881439777)
      ·
        refine ⟨25544026286400981661079833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34058701715201308881439777 25544026286400981661079833)
        ·
          refine ⟨19158019714800736245809875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25544026286400981661079833 19158019714800736245809875)
          ·
            refine ⟨28737029572201104368714813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19158019714800736245809875 28737029572201104368714813)
            ·
              refine ⟨10776386089575414138268055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28737029572201104368714813 10776386089575414138268055)
              ·
                refine ⟨16164579134363121207402083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776386089575414138268055 16164579134363121207402083)
                ·
                  refine ⟨24246868701544681811103125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16164579134363121207402083 24246868701544681811103125)
                  ·
                    refine ⟨1136571970384906959895459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24246868701544681811103125 1136571970384906959895459)
                    ·
                      rfl

theorem cell22_3320199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3320199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320199 prefixEnd_3320199 := by exact prefixLift 3320199
  have htrace : WordTrace (prefixWord ++ tailWord_3320199) baseStart_3320199 baseEnd_3320199 := by
    simpa [prefixWord, tailWord_3320199, baseEnd_3320199] using wordTrace_append hprefix tailTrace_3320199
  have hstable : (prefixWord ++ tailWord_3320199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320199).length < 2 ^ (prefixWord ++ tailWord_3320199).sum := by decide
  have hdescent : baseEnd_3320199 < baseStart_3320199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320218 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_3320218 : Nat := 118140960795 + 3320218 * 2 ^ 59
def prefixEnd_3320218 : Nat := 4983230072969 + 3 ^ 40 * 3320218 * 2
def baseEnd_3320218 : Nat := 1136578474473197243670401

theorem tailTrace_3320218 : CollatzResearch.WordTrace tailWord_3320218 prefixEnd_3320218 1136578474473197243670401 := by
  unfold tailWord_3320218
  simp only [CollatzResearch.WordTrace]
  refine ⟨30274574771356177233626327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80732199390283139289670205 30274574771356177233626327)
  ·
    refine ⟨45411862157034265850439491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30274574771356177233626327 45411862157034265850439491)
    ·
      refine ⟨68117793235551398775659237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45411862157034265850439491 68117793235551398775659237)
      ·
        refine ⟨12772086231665887270436107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68117793235551398775659237 12772086231665887270436107)
        ·
          refine ⟨19158129347498830905654161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12772086231665887270436107 19158129347498830905654161)
          ·
            refine ⟨14368597010624123179240621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19158129347498830905654161 14368597010624123179240621)
            ·
              refine ⟨5388223878984046192215233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14368597010624123179240621 5388223878984046192215233)
              ·
                refine ⟨4041167909238034644161425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388223878984046192215233 4041167909238034644161425)
                ·
                  refine ⟨3030875931928525983121069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4041167909238034644161425 3030875931928525983121069)
                  ·
                    refine ⟨1136578474473197243670401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030875931928525983121069 1136578474473197243670401)
                    ·
                      rfl

theorem cell22_3320218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_3320218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320218 prefixEnd_3320218 := by exact prefixLift 3320218
  have htrace : WordTrace (prefixWord ++ tailWord_3320218) baseStart_3320218 baseEnd_3320218 := by
    simpa [prefixWord, tailWord_3320218, baseEnd_3320218] using wordTrace_append hprefix tailTrace_3320218
  have hstable : (prefixWord ++ tailWord_3320218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320218).length < 2 ^ (prefixWord ++ tailWord_3320218).sum := by decide
  have hdescent : baseEnd_3320218 < baseStart_3320218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320276 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 7]
def baseStart_3320276 : Nat := 118140960795 + 3320276 * 2 ^ 59
def prefixEnd_3320276 : Nat := 4983230072969 + 3 ^ 40 * 3320276 * 2
def baseEnd_3320276 : Nat := 378866109686168141906741

theorem tailTrace_3320276 : CollatzResearch.WordTrace tailWord_3320276 prefixEnd_3320276 378866109686168141906741 := by
  unfold tailWord_3320276
  simp only [CollatzResearch.WordTrace]
  refine ⟨60550207259607292420058341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80733609679476389893411121 60550207259607292420058341)
  ·
    refine ⟨11353163861176367328760939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60550207259607292420058341 11353163861176367328760939)
    ·
      refine ⟨17029745791764550993141409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11353163861176367328760939 17029745791764550993141409)
      ·
        refine ⟨12772309343823413244856057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17029745791764550993141409 12772309343823413244856057)
        ·
          refine ⟨9579232007867559933642043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12772309343823413244856057 9579232007867559933642043)
          ·
            refine ⟨14368848011801339900463065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9579232007867559933642043 14368848011801339900463065)
            ·
              refine ⟨10776636008851004925347299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14368848011801339900463065 10776636008851004925347299)
              ·
                refine ⟨16164954013276507388020949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776636008851004925347299 16164954013276507388020949)
                ·
                  refine ⟨378866109686168141906741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16164954013276507388020949 378866109686168141906741)
                  ·
                    rfl

theorem cell22_3320276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_3320276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320276 prefixEnd_3320276 := by exact prefixLift 3320276
  have htrace : WordTrace (prefixWord ++ tailWord_3320276) baseStart_3320276 baseEnd_3320276 := by
    simpa [prefixWord, tailWord_3320276, baseEnd_3320276] using wordTrace_append hprefix tailTrace_3320276
  have hstable : (prefixWord ++ tailWord_3320276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320276).length < 2 ^ (prefixWord ++ tailWord_3320276).sum := by decide
  have hdescent : baseEnd_3320276 < baseStart_3320276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320293 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 5]
def baseStart_3320293 : Nat := 118140960795 + 3320293 * 2 ^ 59
def prefixEnd_3320293 : Nat := 4983230072969 + 3 ^ 40 * 3320293 * 2
def baseEnd_3320293 : Nat := 378868049501974016015057

theorem tailTrace_3320293 : CollatzResearch.WordTrace tailWord_3320293 prefixEnd_3320293 378868049501974016015057 := by
  unfold tailWord_3320293
  simp only [CollatzResearch.WordTrace]
  refine ⟨121101034560152996743485533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80734023040101997828990355 121101034560152996743485533)
  ·
    refine ⟨45412887960057373778807075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121101034560152996743485533 45412887960057373778807075)
    ·
      refine ⟨68119331940086060668210613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45412887960057373778807075 68119331940086060668210613)
      ·
        refine ⟨6386187369383068187644745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68119331940086060668210613 6386187369383068187644745)
        ·
          refine ⟨4789640527037301140733559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6386187369383068187644745 4789640527037301140733559)
          ·
            refine ⟨7184460790555951711100339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789640527037301140733559 7184460790555951711100339)
            ·
              refine ⟨10776691185833927566650509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184460790555951711100339 10776691185833927566650509)
              ·
                refine ⟨4041259194687722837493941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10776691185833927566650509 4041259194687722837493941)
                ·
                  refine ⟨378868049501974016015057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4041259194687722837493941 378868049501974016015057)
                  ·
                    rfl

theorem cell22_3320293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_3320293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320293 prefixEnd_3320293 := by exact prefixLift 3320293
  have htrace : WordTrace (prefixWord ++ tailWord_3320293) baseStart_3320293 baseEnd_3320293 := by
    simpa [prefixWord, tailWord_3320293, baseEnd_3320293] using wordTrace_append hprefix tailTrace_3320293
  have hstable : (prefixWord ++ tailWord_3320293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320293).length < 2 ^ (prefixWord ++ tailWord_3320293).sum := by decide
  have hdescent : baseEnd_3320293 < baseStart_3320293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320304 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 8]
def baseStart_3320304 : Nat := 118140960795 + 3320304 * 2 ^ 59
def prefixEnd_3320304 : Nat := 4983230072969 + 3 ^ 40 * 3320304 * 2
def baseEnd_3320304 : Nat := 378869304676907228673379

theorem tailTrace_3320304 : CollatzResearch.WordTrace tailWord_3320304 prefixEnd_3320304 378869304676907228673379 := by
  unfold tailWord_3320304
  simp only [CollatzResearch.WordTrace]
  refine ⟨60550717881556572811067983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80734290508742097081423977 60550717881556572811067983)
  ·
    refine ⟨90826076822334859216601975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60550717881556572811067983 90826076822334859216601975)
    ·
      refine ⟨136239115233502288824902963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90826076822334859216601975 136239115233502288824902963)
      ·
        refine ⟨204358672850253433237354445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136239115233502288824902963 204358672850253433237354445)
        ·
          refine ⟨76634502318845037464007917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204358672850253433237354445 76634502318845037464007917)
          ·
            refine ⟨28737938369566889049002969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76634502318845037464007917 28737938369566889049002969)
            ·
              refine ⟨21553453777175166786752227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28737938369566889049002969 21553453777175166786752227)
              ·
                refine ⟨32330180665762750180128341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21553453777175166786752227 32330180665762750180128341)
                ·
                  refine ⟨378869304676907228673379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32330180665762750180128341 378869304676907228673379)
                  ·
                    rfl

theorem cell22_3320304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_3320304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320304 prefixEnd_3320304 := by exact prefixLift 3320304
  have htrace : WordTrace (prefixWord ++ tailWord_3320304) baseStart_3320304 baseEnd_3320304 := by
    simpa [prefixWord, tailWord_3320304, baseEnd_3320304] using wordTrace_append hprefix tailTrace_3320304
  have hstable : (prefixWord ++ tailWord_3320304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320304).length < 2 ^ (prefixWord ++ tailWord_3320304).sum := by decide
  have hdescent : baseEnd_3320304 < baseStart_3320304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320323 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 1, 4]
def baseStart_3320323 : Nat := 118140960795 + 3320323 * 2 ^ 59
def prefixEnd_3320323 : Nat := 4983230072969 + 3 ^ 40 * 3320323 * 2
def baseEnd_3320323 : Nat := 1136614418119011969795079

theorem tailTrace_3320323 : CollatzResearch.WordTrace tailWord_3320323 prefixEnd_3320323 1136614418119011969795079 := by
  unfold tailWord_3320323
  simp only [CollatzResearch.WordTrace]
  refine ⟨121102128750044311867077623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80734752500029541244718415 121102128750044311867077623)
  ·
    refine ⟨181653193125066467800616435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121102128750044311867077623 181653193125066467800616435)
    ·
      refine ⟨272479789687599701700924653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181653193125066467800616435 272479789687599701700924653)
      ·
        refine ⟨102179921132849888137846745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272479789687599701700924653 102179921132849888137846745)
        ·
          refine ⟨76634940849637416103385059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102179921132849888137846745 76634940849637416103385059)
          ·
            refine ⟨114952411274456124155077589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76634940849637416103385059 114952411274456124155077589)
            ·
              refine ⟨2694197139245065409884631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 114952411274456124155077589 2694197139245065409884631)
              ·
                refine ⟨4041295708867598114826947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694197139245065409884631 4041295708867598114826947)
                ·
                  refine ⟨6061943563301397172240421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041295708867598114826947 6061943563301397172240421)
                  ·
                    refine ⟨1136614418119011969795079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6061943563301397172240421 1136614418119011969795079)
                    ·
                      rfl

theorem cell22_3320323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 4].length) (baseStart_3320323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320323 prefixEnd_3320323 := by exact prefixLift 3320323
  have htrace : WordTrace (prefixWord ++ tailWord_3320323) baseStart_3320323 baseEnd_3320323 := by
    simpa [prefixWord, tailWord_3320323, baseEnd_3320323] using wordTrace_append hprefix tailTrace_3320323
  have hstable : (prefixWord ++ tailWord_3320323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320323).length < 2 ^ (prefixWord ++ tailWord_3320323).sum := by decide
  have hdescent : baseEnd_3320323 < baseStart_3320323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320353 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3320353 : Nat := 118140960795 + 3320353 * 2 ^ 59
def prefixEnd_3320353 : Nat := 4983230072969 + 3 ^ 40 * 3320353 * 2
def baseEnd_3320353 : Nat := 1136624687732101891544987

theorem tailTrace_3320353 : CollatzResearch.WordTrace tailWord_3320353 prefixEnd_3320353 1136624687732101891544987 := by
  unfold tailWord_3320353
  simp only [CollatzResearch.WordTrace]
  refine ⟨121103222939935626990669713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80735481959957084660446475 121103222939935626990669713)
  ·
    refine ⟨90827417204951720243002285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121103222939935626990669713 90827417204951720243002285)
    ·
      refine ⟨34060281451856895091125857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90827417204951720243002285 34060281451856895091125857)
      ·
        refine ⟨25545211088892671318344393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34060281451856895091125857 25545211088892671318344393)
        ·
          refine ⟨19158908316669503488758295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25545211088892671318344393 19158908316669503488758295)
          ·
            refine ⟨28738362475004255233137443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19158908316669503488758295 28738362475004255233137443)
            ·
              refine ⟨43107543712506382849706165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28738362475004255233137443 43107543712506382849706165)
              ·
                refine ⟨4041332223047473392159953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43107543712506382849706165 4041332223047473392159953)
                ·
                  refine ⟨3030999167285605044119965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4041332223047473392159953 3030999167285605044119965)
                  ·
                    refine ⟨1136624687732101891544987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3030999167285605044119965 1136624687732101891544987)
                    ·
                      rfl

theorem cell22_3320353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3320353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320353 prefixEnd_3320353 := by exact prefixLift 3320353
  have htrace : WordTrace (prefixWord ++ tailWord_3320353) baseStart_3320353 baseEnd_3320353 := by
    simpa [prefixWord, tailWord_3320353, baseEnd_3320353] using wordTrace_append hprefix tailTrace_3320353
  have hstable : (prefixWord ++ tailWord_3320353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320353).length < 2 ^ (prefixWord ++ tailWord_3320353).sum := by decide
  have hdescent : baseEnd_3320353 < baseStart_3320353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320398 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3320398 : Nat := 118140960795 + 3320398 * 2 ^ 59
def prefixEnd_3320398 : Nat := 4983230072969 + 3 ^ 40 * 3320398 * 2
def baseEnd_3320398 : Nat := 1136640092151736774169849

theorem tailTrace_3320398 : CollatzResearch.WordTrace tailWord_3320398 prefixEnd_3320398 1136640092151736774169849 := by
  unfold tailWord_3320398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138108028096574959507231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80736576149848399784038565 15138108028096574959507231)
  ·
    refine ⟨22707162042144862439260847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15138108028096574959507231 22707162042144862439260847)
    ·
      refine ⟨34060743063217293658891271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22707162042144862439260847 34060743063217293658891271)
      ·
        refine ⟨51091114594825940488336907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34060743063217293658891271 51091114594825940488336907)
        ·
          refine ⟨76636671892238910732505361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51091114594825940488336907 76636671892238910732505361)
          ·
            refine ⟨57477503919179183049379021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76636671892238910732505361 57477503919179183049379021)
            ·
              refine ⟨21554063969692193643517133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57477503919179183049379021 21554063969692193643517133)
              ·
                refine ⟨8082773988634572616318925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21554063969692193643517133 8082773988634572616318925)
                ·
                  refine ⟨3031040245737964731119597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8082773988634572616318925 3031040245737964731119597)
                  ·
                    refine ⟨1136640092151736774169849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031040245737964731119597 1136640092151736774169849)
                    ·
                      rfl

theorem cell22_3320398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3320398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320398 prefixEnd_3320398 := by exact prefixLift 3320398
  have htrace : WordTrace (prefixWord ++ tailWord_3320398) baseStart_3320398 baseEnd_3320398 := by
    simpa [prefixWord, tailWord_3320398, baseEnd_3320398] using wordTrace_append hprefix tailTrace_3320398
  have hstable : (prefixWord ++ tailWord_3320398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320398).length < 2 ^ (prefixWord ++ tailWord_3320398).sum := by decide
  have hdescent : baseEnd_3320398 < baseStart_3320398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320593 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_3320593 : Nat := 118140960795 + 3320593 * 2 ^ 59
def prefixEnd_3320593 : Nat := 4983230072969 + 3 ^ 40 * 3320593 * 2
def baseEnd_3320593 : Nat := 1136706844636821265544251

theorem tailTrace_3320593 : CollatzResearch.WordTrace tailWord_3320593 prefixEnd_3320593 1136706844636821265544251 := by
  unfold tailWord_3320593
  simp only [CollatzResearch.WordTrace]
  refine ⟨121111976459066147979406433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80741317639377431986270955 121111976459066147979406433)
  ·
    refine ⟨90833982344299610984554825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121111976459066147979406433 90833982344299610984554825)
    ·
      refine ⟨68125486758224708238416119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90833982344299610984554825 68125486758224708238416119)
      ·
        refine ⟨102188230137337062357624179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68125486758224708238416119 102188230137337062357624179)
        ·
          refine ⟨153282345206005593536436269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102188230137337062357624179 153282345206005593536436269)
          ·
            refine ⟨57480879452252097576163601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153282345206005593536436269 57480879452252097576163601)
            ·
              refine ⟨43110659589189073182122701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57480879452252097576163601 43110659589189073182122701)
              ·
                refine ⟨16166497345945902443296013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43110659589189073182122701 16166497345945902443296013)
                ·
                  refine ⟨6062436504729713416236005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16166497345945902443296013 6062436504729713416236005)
                  ·
                    refine ⟨1136706844636821265544251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6062436504729713416236005 1136706844636821265544251)
                    ·
                      rfl

theorem cell22_3320593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_3320593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320593 prefixEnd_3320593 := by exact prefixLift 3320593
  have htrace : WordTrace (prefixWord ++ tailWord_3320593) baseStart_3320593 baseEnd_3320593 := by
    simpa [prefixWord, tailWord_3320593, baseEnd_3320593] using wordTrace_append hprefix tailTrace_3320593
  have hstable : (prefixWord ++ tailWord_3320593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320593).length < 2 ^ (prefixWord ++ tailWord_3320593).sum := by decide
  have hdescent : baseEnd_3320593 < baseStart_3320593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320618 : List Nat := [3, 1, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3320618 : Nat := 118140960795 + 3320618 * 2 ^ 59
def prefixEnd_3320618 : Nat := 4983230072969 + 3 ^ 40 * 3320618 * 2
def baseEnd_3320618 : Nat := 1136715402647729533669175

theorem tailTrace_3320618 : CollatzResearch.WordTrace tailWord_3320618 prefixEnd_3320618 1136715402647729533669175 := by
  unfold tailWord_3320618
  simp only [CollatzResearch.WordTrace]
  refine ⟨30278222070993894312266627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80741925522650384832711005 30278222070993894312266627)
  ·
    refine ⟨45417333106490841468399941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30278222070993894312266627 45417333106490841468399941)
    ·
      refine ⟨8515749957467032775324989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45417333106490841468399941 8515749957467032775324989)
      ·
        refine ⟨3193406234050137290746871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8515749957467032775324989 3193406234050137290746871)
        ·
          refine ⟨4790109351075205936120307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193406234050137290746871 4790109351075205936120307)
          ·
            refine ⟨7185164026612808904180461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790109351075205936120307 7185164026612808904180461)
            ·
              refine ⟨2694436509979803339067673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7185164026612808904180461 2694436509979803339067673)
              ·
                refine ⟨2020827382484852504300755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694436509979803339067673 2020827382484852504300755)
                ·
                  refine ⟨3031241073727278756451133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020827382484852504300755 3031241073727278756451133)
                  ·
                    refine ⟨1136715402647729533669175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031241073727278756451133 1136715402647729533669175)
                    ·
                      rfl

theorem cell22_3320618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3320618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320618 prefixEnd_3320618 := by exact prefixLift 3320618
  have htrace : WordTrace (prefixWord ++ tailWord_3320618) baseStart_3320618 baseEnd_3320618 := by
    simpa [prefixWord, tailWord_3320618, baseEnd_3320618] using wordTrace_append hprefix tailTrace_3320618
  have hstable : (prefixWord ++ tailWord_3320618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320618).length < 2 ^ (prefixWord ++ tailWord_3320618).sum := by decide
  have hdescent : baseEnd_3320618 < baseStart_3320618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320644 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3320644 : Nat := 118140960795 + 3320644 * 2 ^ 59
def prefixEnd_3320644 : Nat := 4983230072969 + 3 ^ 40 * 3320644 * 2
def baseEnd_3320644 : Nat := 1136724302979074132519095

theorem tailTrace_3320644 : CollatzResearch.WordTrace tailWord_3320644 prefixEnd_3320644 1136724302979074132519095 := by
  unfold tailWord_3320644
  simp only [CollatzResearch.WordTrace]
  refine ⟨60556918290940691844756493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80742557721254255793008657 60556918290940691844756493)
  ·
    refine ⟨22708844359102759441783685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60556918290940691844756493 22708844359102759441783685)
    ·
      refine ⟨4257908317331767395334441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22708844359102759441783685 4257908317331767395334441)
      ·
        refine ⟨3193431237998825546500831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257908317331767395334441 3193431237998825546500831)
        ·
          refine ⟨4790146856998238319751247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193431237998825546500831 4790146856998238319751247)
          ·
            refine ⟨7185220285497357479626871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790146856998238319751247 7185220285497357479626871)
            ·
              refine ⟨10777830428246036219440307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185220285497357479626871 10777830428246036219440307)
              ·
                refine ⟨16166745642369054329160461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10777830428246036219440307 16166745642369054329160461)
                ·
                  refine ⟨6062529615888395373435173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16166745642369054329160461 6062529615888395373435173)
                  ·
                    refine ⟨1136724302979074132519095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6062529615888395373435173 1136724302979074132519095)
                    ·
                      rfl

theorem cell22_3320644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3320644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320644 prefixEnd_3320644 := by exact prefixLift 3320644
  have htrace : WordTrace (prefixWord ++ tailWord_3320644) baseStart_3320644 baseEnd_3320644 := by
    simpa [prefixWord, tailWord_3320644, baseEnd_3320644] using wordTrace_append hprefix tailTrace_3320644
  have hstable : (prefixWord ++ tailWord_3320644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320644).length < 2 ^ (prefixWord ++ tailWord_3320644).sum := by decide
  have hdescent : baseEnd_3320644 < baseStart_3320644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320683 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 2, 6]
def baseStart_3320683 : Nat := 118140960795 + 3320683 * 2 ^ 59
def prefixEnd_3320683 : Nat := 4983230072969 + 3 ^ 40 * 3320683 * 2
def baseEnd_3320683 : Nat := 1136737653476091030793975

theorem tailTrace_3320683 : CollatzResearch.WordTrace tailWord_3320683 prefixEnd_3320683 1136737653476091030793975 := by
  unfold tailWord_3320683
  simp only [CollatzResearch.WordTrace]
  refine ⟨121115259028740093350182703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80743506019160062233455135 121115259028740093350182703)
  ·
    refine ⟨181672888543110140025274055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121115259028740093350182703 181672888543110140025274055)
    ·
      refine ⟨272509332814665210037911083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181672888543110140025274055 272509332814665210037911083)
      ·
        refine ⟨408763999221997815056866625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272509332814665210037911083 408763999221997815056866625)
        ·
          refine ⟨306572999416498361292649969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408763999221997815056866625 306572999416498361292649969)
          ·
            refine ⟨229929749562373770969487477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306572999416498361292649969 229929749562373770969487477)
            ·
              refine ⟨21555914021472541028389451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229929749562373770969487477 21555914021472541028389451)
              ·
                refine ⟨32333871032208811542584177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21555914021472541028389451 32333871032208811542584177)
                ·
                  refine ⟨24250403274156608656938133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32333871032208811542584177 24250403274156608656938133)
                  ·
                    refine ⟨1136737653476091030793975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24250403274156608656938133 1136737653476091030793975)
                    ·
                      rfl

theorem cell22_3320683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_3320683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320683 prefixEnd_3320683 := by exact prefixLift 3320683
  have htrace : WordTrace (prefixWord ++ tailWord_3320683) baseStart_3320683 baseEnd_3320683 := by
    simpa [prefixWord, tailWord_3320683, baseEnd_3320683] using wordTrace_append hprefix tailTrace_3320683
  have hstable : (prefixWord ++ tailWord_3320683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320683).length < 2 ^ (prefixWord ++ tailWord_3320683).sum := by decide
  have hdescent : baseEnd_3320683 < baseStart_3320683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320698 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_3320698 : Nat := 118140960795 + 3320698 * 2 ^ 59
def prefixEnd_3320698 : Nat := 4983230072969 + 3 ^ 40 * 3320698 * 2
def baseEnd_3320698 : Nat := 378914262760878663889643

theorem tailTrace_3320698 : CollatzResearch.WordTrace tailWord_3320698 prefixEnd_3320698 378914262760878663889643 := by
  unfold tailWord_3320698
  simp only [CollatzResearch.WordTrace]
  refine ⟨30278951530921437727994687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80743870749123833941319165 30278951530921437727994687)
  ·
    refine ⟨45418427296382156591992031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30278951530921437727994687 45418427296382156591992031)
    ·
      refine ⟨68127640944573234887988047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45418427296382156591992031 68127640944573234887988047)
      ·
        refine ⟨102191461416859852331982071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68127640944573234887988047 102191461416859852331982071)
        ·
          refine ⟨153287192125289778497973107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102191461416859852331982071 153287192125289778497973107)
          ·
            refine ⟨229930788187934667746959661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153287192125289778497973107 229930788187934667746959661)
            ·
              refine ⟨86224045570475500405109873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229930788187934667746959661 86224045570475500405109873)
              ·
                refine ⟨64668034177856625303832405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86224045570475500405109873 64668034177856625303832405)
                ·
                  refine ⟨378914262760878663889643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64668034177856625303832405 378914262760878663889643)
                  ·
                    rfl

theorem cell22_3320698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_3320698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320698 prefixEnd_3320698 := by exact prefixLift 3320698
  have htrace : WordTrace (prefixWord ++ tailWord_3320698) baseStart_3320698 baseEnd_3320698 := by
    simpa [prefixWord, tailWord_3320698, baseEnd_3320698] using wordTrace_append hprefix tailTrace_3320698
  have hstable : (prefixWord ++ tailWord_3320698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320698).length < 2 ^ (prefixWord ++ tailWord_3320698).sum := by decide
  have hdescent : baseEnd_3320698 < baseStart_3320698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320732 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 7]
def baseStart_3320732 : Nat := 118140960795 + 3320732 * 2 ^ 59
def prefixEnd_3320732 : Nat := 4983230072969 + 3 ^ 40 * 3320732 * 2
def baseEnd_3320732 : Nat := 378918142392490412106275

theorem tailTrace_3320732 : CollatzResearch.WordTrace tailWord_3320732 prefixEnd_3320732 378918142392490412106275 := by
  unfold tailWord_3320732
  simp only [CollatzResearch.WordTrace]
  refine ⟨60558523102781287359358225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80744697470375049812477633 60558523102781287359358225)
  ·
    refine ⟨45418892327085965519518669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60558523102781287359358225 45418892327085965519518669)
    ·
      refine ⟨17032084622657237069819501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45418892327085965519518669 17032084622657237069819501)
      ·
        refine ⟨6387031733496463901182313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17032084622657237069819501 6387031733496463901182313)
        ·
          refine ⟨4790273800122347925886735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6387031733496463901182313 4790273800122347925886735)
          ·
            refine ⟨7185410700183521888830103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790273800122347925886735 7185410700183521888830103)
            ·
              refine ⟨10778116050275282833245155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185410700183521888830103 10778116050275282833245155)
              ·
                refine ⟨16167174075412924249867733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10778116050275282833245155 16167174075412924249867733)
                ·
                  refine ⟨378918142392490412106275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16167174075412924249867733 378918142392490412106275)
                  ·
                    rfl

theorem cell22_3320732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_3320732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320732 prefixEnd_3320732 := by exact prefixLift 3320732
  have htrace : WordTrace (prefixWord ++ tailWord_3320732) baseStart_3320732 baseEnd_3320732 := by
    simpa [prefixWord, tailWord_3320732, baseEnd_3320732] using wordTrace_append hprefix tailTrace_3320732
  have hstable : (prefixWord ++ tailWord_3320732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320732).length < 2 ^ (prefixWord ++ tailWord_3320732).sum := by decide
  have hdescent : baseEnd_3320732 < baseStart_3320732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320760 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 6]
def baseStart_3320760 : Nat := 118140960795 + 3320760 * 2 ^ 59
def prefixEnd_3320760 : Nat := 4983230072969 + 3 ^ 40 * 3320760 * 2
def baseEnd_3320760 : Nat := 378921337383229498872913

theorem tailTrace_3320760 : CollatzResearch.WordTrace tailWord_3320760 prefixEnd_3320760 378921337383229498872913 := by
  unfold tailWord_3320760
  simp only [CollatzResearch.WordTrace]
  refine ⟨60559033724730567750367867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80745378299640757000490489 60559033724730567750367867)
  ·
    refine ⟨90838550587095851625551801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60559033724730567750367867 90838550587095851625551801)
    ·
      refine ⟨68128912940321888719163851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90838550587095851625551801 68128912940321888719163851)
      ·
        refine ⟨102193369410482833078745777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68128912940321888719163851 102193369410482833078745777)
        ·
          refine ⟨76645027057862124809059333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102193369410482833078745777 76645027057862124809059333)
          ·
            refine ⟨14370942573349148401698625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76645027057862124809059333 14370942573349148401698625)
            ·
              refine ⟨10778206930011861301273969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14370942573349148401698625 10778206930011861301273969)
              ·
                refine ⟨8083655197508895975955477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10778206930011861301273969 8083655197508895975955477)
                ·
                  refine ⟨378921337383229498872913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8083655197508895975955477 378921337383229498872913)
                  ·
                    rfl

theorem cell22_3320760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_3320760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320760 prefixEnd_3320760 := by exact prefixLift 3320760
  have htrace : WordTrace (prefixWord ++ tailWord_3320760) baseStart_3320760 baseEnd_3320760 := by
    simpa [prefixWord, tailWord_3320760, baseEnd_3320760] using wordTrace_append hprefix tailTrace_3320760
  have hstable : (prefixWord ++ tailWord_3320760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320760).length < 2 ^ (prefixWord ++ tailWord_3320760).sum := by decide
  have hdescent : baseEnd_3320760 < baseStart_3320760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320762 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_3320762 : Nat := 118140960795 + 3320762 * 2 ^ 59
def prefixEnd_3320762 : Nat := 4983230072969 + 3 ^ 40 * 3320762 * 2
def baseEnd_3320762 : Nat := 1136764696790561158068733

theorem tailTrace_3320762 : CollatzResearch.WordTrace tailWord_3320762 prefixEnd_3320762 1136764696790561158068733 := by
  unfold tailWord_3320762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30279535098863472460577135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80745426930302593228205693 30279535098863472460577135)
  ·
    refine ⟨45419302648295208690865703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30279535098863472460577135 45419302648295208690865703)
    ·
      refine ⟨68128953972442813036298555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45419302648295208690865703 68128953972442813036298555)
      ·
        refine ⟨102193430958664219554447833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68128953972442813036298555 102193430958664219554447833)
        ·
          refine ⟨76645073218998164665835875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102193430958664219554447833 76645073218998164665835875)
          ·
            refine ⟨114967609828497246998753813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76645073218998164665835875 114967609828497246998753813)
            ·
              refine ⟨5389106710710808453066585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114967609828497246998753813 5389106710710808453066585)
              ·
                refine ⟨4041830033033106339799939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389106710710808453066585 4041830033033106339799939)
                ·
                  refine ⟨6062745049549659509699909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041830033033106339799939 6062745049549659509699909)
                  ·
                    refine ⟨1136764696790561158068733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6062745049549659509699909 1136764696790561158068733)
                    ·
                      rfl

theorem cell22_3320762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_3320762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320762 prefixEnd_3320762 := by exact prefixLift 3320762
  have htrace : WordTrace (prefixWord ++ tailWord_3320762) baseStart_3320762 baseEnd_3320762 := by
    simpa [prefixWord, tailWord_3320762, baseEnd_3320762] using wordTrace_append hprefix tailTrace_3320762
  have hstable : (prefixWord ++ tailWord_3320762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320762).length < 2 ^ (prefixWord ++ tailWord_3320762).sum := by decide
  have hdescent : baseEnd_3320762 < baseStart_3320762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320775 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3320775 : Nat := 118140960795 + 3320775 * 2 ^ 59
def prefixEnd_3320775 : Nat := 4983230072969 + 3 ^ 40 * 3320775 * 2
def baseEnd_3320775 : Nat := 1136769146956233457493693

theorem tailTrace_3320775 : CollatzResearch.WordTrace tailWord_3320775 prefixEnd_3320775 1136769146956233457493693 := by
  unfold tailWord_3320775
  simp only [CollatzResearch.WordTrace]
  refine ⟨121118614544406793062531779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80745743029604528708354519 121118614544406793062531779)
  ·
    refine ⟨181677921816610189593797669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121118614544406793062531779 181677921816610189593797669)
    ·
      refine ⟨34064610340614410548837063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181677921816610189593797669 34064610340614410548837063)
      ·
        refine ⟨51096915510921615823255595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34064610340614410548837063 51096915510921615823255595)
        ·
          refine ⟨76645373266382423734883393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51096915510921615823255595 76645373266382423734883393)
          ·
            refine ⟨57484029949786817801162545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76645373266382423734883393 57484029949786817801162545)
            ·
              refine ⟨43113022462340113350871909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57484029949786817801162545 43113022462340113350871909)
              ·
                refine ⟨8083691711688771253288483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43113022462340113350871909 8083691711688771253288483)
                ·
                  refine ⟨12125537567533156879932725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083691711688771253288483 12125537567533156879932725)
                  ·
                    refine ⟨1136769146956233457493693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12125537567533156879932725 1136769146956233457493693)
                    ·
                      rfl

theorem cell22_3320775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3320775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320775 prefixEnd_3320775 := by exact prefixLift 3320775
  have htrace : WordTrace (prefixWord ++ tailWord_3320775) baseStart_3320775 baseEnd_3320775 := by
    simpa [prefixWord, tailWord_3320775, baseEnd_3320775] using wordTrace_append hprefix tailTrace_3320775
  have hstable : (prefixWord ++ tailWord_3320775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320775).length < 2 ^ (prefixWord ++ tailWord_3320775).sum := by decide
  have hdescent : baseEnd_3320775 < baseStart_3320775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320792 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 4, 3]
def baseStart_3320792 : Nat := 118140960795 + 3320792 * 2 ^ 59
def prefixEnd_3320792 : Nat := 4983230072969 + 3 ^ 40 * 3320792 * 2
def baseEnd_3320792 : Nat := 1136774966403651079818641

theorem tailTrace_3320792 : CollatzResearch.WordTrace tailWord_3320792 prefixEnd_3320792 1136774966403651079818641 := by
  unfold tailWord_3320792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60559617292672602482950315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80746156390230136643933753 60559617292672602482950315)
  ·
    refine ⟨90839425939008903724425473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60559617292672602482950315 90839425939008903724425473)
    ·
      refine ⟨68129569454256677793319105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90839425939008903724425473 68129569454256677793319105)
      ·
        refine ⟨51097177090692508344989329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68129569454256677793319105 51097177090692508344989329)
        ·
          refine ⟨38322882818019381258741997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51097177090692508344989329 38322882818019381258741997)
          ·
            refine ⟨14371081056757267972028249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38322882818019381258741997 14371081056757267972028249)
            ·
              refine ⟨10778310792567950979021187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14371081056757267972028249 10778310792567950979021187)
              ·
                refine ⟨16167466188851926468531781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10778310792567950979021187 16167466188851926468531781)
                ·
                  refine ⟨3031399910409736212849709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16167466188851926468531781 3031399910409736212849709)
                  ·
                    refine ⟨1136774966403651079818641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031399910409736212849709 1136774966403651079818641)
                    ·
                      rfl

theorem cell22_3320792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_3320792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320792 prefixEnd_3320792 := by exact prefixLift 3320792
  have htrace : WordTrace (prefixWord ++ tailWord_3320792) baseStart_3320792 baseEnd_3320792 := by
    simpa [prefixWord, tailWord_3320792, baseEnd_3320792] using wordTrace_append hprefix tailTrace_3320792
  have hstable : (prefixWord ++ tailWord_3320792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320792).length < 2 ^ (prefixWord ++ tailWord_3320792).sum := by decide
  have hdescent : baseEnd_3320792 < baseStart_3320792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320822 : List Nat := [5, 1, 1, 1, 3, 1, 2, 8]
def baseStart_3320822 : Nat := 118140960795 + 3320822 * 2 ^ 59
def prefixEnd_3320822 : Nat := 4983230072969 + 3 ^ 40 * 3320822 * 2
def baseEnd_3320822 : Nat := 126309470668526777952061

theorem tailTrace_3320822 : CollatzResearch.WordTrace tailWord_3320822 prefixEnd_3320822 126309470668526777952061 := by
  unfold tailWord_3320822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570020548452282505593295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80746885850157680059661813 7570020548452282505593295)
  ·
    refine ⟨11355030822678423758389943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7570020548452282505593295 11355030822678423758389943)
    ·
      refine ⟨17032546234017635637584915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11355030822678423758389943 17032546234017635637584915)
      ·
        refine ⟨25548819351026453456377373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17032546234017635637584915 25548819351026453456377373)
        ·
          refine ⟨9580807256634920046141515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25548819351026453456377373 9580807256634920046141515)
          ·
            refine ⟨14371210884952380069212273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580807256634920046141515 14371210884952380069212273)
            ·
              refine ⟨10778408163714285051909205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14371210884952380069212273 10778408163714285051909205)
              ·
                refine ⟨126309470668526777952061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10778408163714285051909205 126309470668526777952061)
                ·
                  rfl

theorem cell22_3320822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_3320822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320822 prefixEnd_3320822 := by exact prefixLift 3320822
  have htrace : WordTrace (prefixWord ++ tailWord_3320822) baseStart_3320822 baseEnd_3320822 := by
    simpa [prefixWord, tailWord_3320822, baseEnd_3320822] using wordTrace_append hprefix tailTrace_3320822
  have hstable : (prefixWord ++ tailWord_3320822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320822).length < 2 ^ (prefixWord ++ tailWord_3320822).sum := by decide
  have hdescent : baseEnd_3320822 < baseStart_3320822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320867 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 5]
def baseStart_3320867 : Nat := 118140960795 + 3320867 * 2 ^ 59
def prefixEnd_3320867 : Nat := 4983230072969 + 3 ^ 40 * 3320867 * 2
def baseEnd_3320867 : Nat := 378933546812125294731137

theorem tailTrace_3320867 : CollatzResearch.WordTrace tailWord_3320867 prefixEnd_3320867 378933546812125294731137 := by
  unfold tailWord_3320867
  simp only [CollatzResearch.WordTrace]
  refine ⟨121121970060073492774880855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80747980040048995183253903 121121970060073492774880855)
  ·
    refine ⟨181682955090110239162321283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121121970060073492774880855 181682955090110239162321283)
    ·
      refine ⟨272524432635165358743481925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181682955090110239162321283 272524432635165358743481925)
      ·
        refine ⟨51098331119093504764402861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272524432635165358743481925 51098331119093504764402861)
        ·
          refine ⟨19161874169660064286651073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51098331119093504764402861 19161874169660064286651073)
          ·
            refine ⟨14371405627245048214988305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19161874169660064286651073 14371405627245048214988305)
            ·
              refine ⟨10778554220433786161241229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14371405627245048214988305 10778554220433786161241229)
              ·
                refine ⟨4041957832662669810465461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10778554220433786161241229 4041957832662669810465461)
                ·
                  refine ⟨378933546812125294731137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4041957832662669810465461 378933546812125294731137)
                  ·
                    rfl

theorem cell22_3320867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 5].length) (baseStart_3320867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320867 prefixEnd_3320867 := by exact prefixLift 3320867
  have htrace : WordTrace (prefixWord ++ tailWord_3320867) baseStart_3320867 baseEnd_3320867 := by
    simpa [prefixWord, tailWord_3320867, baseEnd_3320867] using wordTrace_append hprefix tailTrace_3320867
  have hstable : (prefixWord ++ tailWord_3320867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320867).length < 2 ^ (prefixWord ++ tailWord_3320867).sum := by decide
  have hdescent : baseEnd_3320867 < baseStart_3320867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320871 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3320871 : Nat := 118140960795 + 3320871 * 2 ^ 59
def prefixEnd_3320871 : Nat := 4983230072969 + 3 ^ 40 * 3320871 * 2
def baseEnd_3320871 : Nat := 1136802009718121207093399

theorem tailTrace_3320871 : CollatzResearch.WordTrace tailWord_3320871 prefixEnd_3320871 1136802009718121207093399 := by
  unfold tailWord_3320871
  simp only [CollatzResearch.WordTrace]
  refine ⟨121122115952059001458026467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80748077301372667638684311 121122115952059001458026467)
  ·
    refine ⟨181683173928088502187039701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121122115952059001458026467 181683173928088502187039701)
    ·
      refine ⟨4258199388939574270008743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 181683173928088502187039701 4258199388939574270008743)
      ·
        refine ⟨6387299083409361405013115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258199388939574270008743 6387299083409361405013115)
        ·
          refine ⟨9580948625114042107519673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387299083409361405013115 9580948625114042107519673)
          ·
            refine ⟨7185711468835531580639755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9580948625114042107519673 7185711468835531580639755)
            ·
              refine ⟨10778567203253297370959633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185711468835531580639755 10778567203253297370959633)
              ·
                refine ⟨8083925402439973028219725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10778567203253297370959633 8083925402439973028219725)
                ·
                  refine ⟨3031472025914989885582397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8083925402439973028219725 3031472025914989885582397)
                  ·
                    refine ⟨1136802009718121207093399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031472025914989885582397 1136802009718121207093399)
                    ·
                      rfl

theorem cell22_3320871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3320871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320871 prefixEnd_3320871 := by exact prefixLift 3320871
  have htrace : WordTrace (prefixWord ++ tailWord_3320871) baseStart_3320871 baseEnd_3320871 := by
    simpa [prefixWord, tailWord_3320871, baseEnd_3320871] using wordTrace_append hprefix tailTrace_3320871
  have hstable : (prefixWord ++ tailWord_3320871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320871).length < 2 ^ (prefixWord ++ tailWord_3320871).sum := by decide
  have hdescent : baseEnd_3320871 < baseStart_3320871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320895 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 10]
def baseStart_3320895 : Nat := 118140960795 + 3320895 * 2 ^ 59
def prefixEnd_3320895 : Nat := 4983230072969 + 3 ^ 40 * 3320895 * 2
def baseEnd_3320895 : Nat := 378936741802864381497775

theorem tailTrace_3320895 : CollatzResearch.WordTrace tailWord_3320895 prefixEnd_3320895 378936741802864381497775 := by
  unfold tailWord_3320895
  simp only [CollatzResearch.WordTrace]
  refine ⟨121122991303972053556900139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80748660869314702371266759 121122991303972053556900139)
  ·
    refine ⟨181684486955958080335350209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121122991303972053556900139 181684486955958080335350209)
    ·
      refine ⟨136263365216968560251512657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181684486955958080335350209 136263365216968560251512657)
      ·
        refine ⟨102197523912726420188634493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136263365216968560251512657 102197523912726420188634493)
        ·
          refine ⟨38324071467272407570737935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102197523912726420188634493 38324071467272407570737935)
          ·
            refine ⟨57486107200908611356106903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38324071467272407570737935 57486107200908611356106903)
            ·
              refine ⟨86229160801362917034160355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57486107200908611356106903 86229160801362917034160355)
              ·
                refine ⟨129343741202044375551240533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86229160801362917034160355 129343741202044375551240533)
                ·
                  refine ⟨378936741802864381497775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129343741202044375551240533 378936741802864381497775)
                  ·
                    rfl

theorem cell22_3320895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 10].length) (baseStart_3320895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320895 prefixEnd_3320895 := by exact prefixLift 3320895
  have htrace : WordTrace (prefixWord ++ tailWord_3320895) baseStart_3320895 baseEnd_3320895 := by
    simpa [prefixWord, tailWord_3320895, baseEnd_3320895] using wordTrace_append hprefix tailTrace_3320895
  have hstable : (prefixWord ++ tailWord_3320895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320895).length < 2 ^ (prefixWord ++ tailWord_3320895).sum := by decide
  have hdescent : baseEnd_3320895 < baseStart_3320895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320974 : List Nat := [4, 1, 1, 3, 2, 2, 2, 7]
def baseStart_3320974 : Nat := 118140960795 + 3320974 * 2 ^ 59
def prefixEnd_3320974 : Nat := 4983230072969 + 3 ^ 40 * 3320974 * 2
def baseEnd_3320974 : Nat := 126315252080340363529787

theorem tailTrace_3320974 : CollatzResearch.WordTrace tailWord_3320974 prefixEnd_3320974 126315252080340363529787 := by
  unfold tailWord_3320974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15140734083835731256128247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80750581780457233366017317 15140734083835731256128247)
  ·
    refine ⟨22711101125753596884192371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15140734083835731256128247 22711101125753596884192371)
    ·
      refine ⟨34066651688630395326288557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22711101125753596884192371 34066651688630395326288557)
      ·
        refine ⟨12774994383236398247358209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34066651688630395326288557 12774994383236398247358209)
        ·
          refine ⟨9581245787427298685518657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12774994383236398247358209 9581245787427298685518657)
          ·
            refine ⟨7185934340570474014138993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9581245787427298685518657 7185934340570474014138993)
            ·
              refine ⟨5389450755427855510604245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7185934340570474014138993 5389450755427855510604245)
              ·
                refine ⟨126315252080340363529787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5389450755427855510604245 126315252080340363529787)
                ·
                  rfl

theorem cell22_3320974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_3320974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320974 prefixEnd_3320974 := by exact prefixLift 3320974
  have htrace : WordTrace (prefixWord ++ tailWord_3320974) baseStart_3320974 baseEnd_3320974 := by
    simpa [prefixWord, tailWord_3320974, baseEnd_3320974] using wordTrace_append hprefix tailTrace_3320974
  have hstable : (prefixWord ++ tailWord_3320974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320974).length < 2 ^ (prefixWord ++ tailWord_3320974).sum := by decide
  have hdescent : baseEnd_3320974 < baseStart_3320974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320978 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3320978 : Nat := 118140960795 + 3320978 * 2 ^ 59
def prefixEnd_3320978 : Nat := 4983230072969 + 3 ^ 40 * 3320978 * 2
def baseEnd_3320978 : Nat := 1136838638004808594668071

theorem tailTrace_3320978 : CollatzResearch.WordTrace tailWord_3320978 prefixEnd_3320978 1136838638004808594668071 := by
  unfold tailWord_3320978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30281504640667839683042897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80750679041780905821447725 30281504640667839683042897)
  ·
    refine ⟨22711128480500879762282173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30281504640667839683042897 22711128480500879762282173)
    ·
      refine ⟨8516673180187829910855815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22711128480500879762282173 8516673180187829910855815)
      ·
        refine ⟨12775009770281744866283723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8516673180187829910855815 12775009770281744866283723)
        ·
          refine ⟨19162514655422617299425585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12775009770281744866283723 19162514655422617299425585)
          ·
            refine ⟨14371885991566962974569189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19162514655422617299425585 14371885991566962974569189)
            ·
              refine ⟨2694728623418805557731723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14371885991566962974569189 2694728623418805557731723)
              ·
                refine ⟨4042092935128208336597585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694728623418805557731723 4042092935128208336597585)
                ·
                  refine ⟨3031569701346156252448189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042092935128208336597585 3031569701346156252448189)
                  ·
                    refine ⟨1136838638004808594668071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031569701346156252448189 1136838638004808594668071)
                    ·
                      rfl

theorem cell22_3320978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3320978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320978 prefixEnd_3320978 := by exact prefixLift 3320978
  have htrace : WordTrace (prefixWord ++ tailWord_3320978) baseStart_3320978 baseEnd_3320978 := by
    simpa [prefixWord, tailWord_3320978, baseEnd_3320978] using wordTrace_append hprefix tailTrace_3320978
  have hstable : (prefixWord ++ tailWord_3320978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320978).length < 2 ^ (prefixWord ++ tailWord_3320978).sum := by decide
  have hdescent : baseEnd_3320978 < baseStart_3320978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320989 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_3320989 : Nat := 118140960795 + 3320989 * 2 ^ 59
def prefixEnd_3320989 : Nat := 4983230072969 + 3 ^ 40 * 3320989 * 2
def baseEnd_3320989 : Nat := 1136842403529608232643037

theorem tailTrace_3320989 : CollatzResearch.WordTrace tailWord_3320989 prefixEnd_3320989 1136842403529608232643037 := by
  unfold tailWord_3320989
  simp only [CollatzResearch.WordTrace]
  refine ⟨121126419765631507610822021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80750946510421005073881347 121126419765631507610822021)
  ·
    refine ⟨22711203706055907677029129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121126419765631507610822021 22711203706055907677029129)
    ·
      refine ⟨17033402779541930757771847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22711203706055907677029129 17033402779541930757771847)
      ·
        refine ⟨25550104169312896136657771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17033402779541930757771847 25550104169312896136657771)
        ·
          refine ⟨38325156253969344204986657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25550104169312896136657771 38325156253969344204986657)
          ·
            refine ⟨28743867190477008153739993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38325156253969344204986657 28743867190477008153739993)
            ·
              refine ⟨21557900392857756115304995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28743867190477008153739993 21557900392857756115304995)
              ·
                refine ⟨32336850589286634172957493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21557900392857756115304995 32336850589286634172957493)
                ·
                  refine ⟨3031579742745621953714765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32336850589286634172957493 3031579742745621953714765)
                  ·
                    refine ⟨1136842403529608232643037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031579742745621953714765 1136842403529608232643037)
                    ·
                      rfl

theorem cell22_3320989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_3320989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3320989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3320989 prefixEnd_3320989 := by exact prefixLift 3320989
  have htrace : WordTrace (prefixWord ++ tailWord_3320989) baseStart_3320989 baseEnd_3320989 := by
    simpa [prefixWord, tailWord_3320989, baseEnd_3320989] using wordTrace_append hprefix tailTrace_3320989
  have hstable : (prefixWord ++ tailWord_3320989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320989).length < 2 ^ (prefixWord ++ tailWord_3320989).sum := by decide
  have hdescent : baseEnd_3320989 < baseStart_3320989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321014 : List Nat := [5, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_3321014 : Nat := 118140960795 + 3321014 * 2 ^ 59
def prefixEnd_3321014 : Nat := 4983230072969 + 3 ^ 40 * 3321014 * 2
def baseEnd_3321014 : Nat := 378950320513505500255987

theorem tailTrace_3321014 : CollatzResearch.WordTrace tailWord_3321014 prefixEnd_3321014 378950320513505500255987 := by
  unfold tailWord_3321014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570458224408808555030131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80751554393693957920321397 7570458224408808555030131)
  ·
    refine ⟨11355687336613212832545197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7570458224408808555030131 11355687336613212832545197)
    ·
      refine ⟨4258382751229954812204449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11355687336613212832545197 4258382751229954812204449)
      ·
        refine ⟨3193787063422466109153337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4258382751229954812204449 3193787063422466109153337)
        ·
          refine ⟨2395340297566849581865003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193787063422466109153337 2395340297566849581865003)
          ·
            refine ⟨3593010446350274372797505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395340297566849581865003 3593010446350274372797505)
            ·
              refine ⟨2694757834762705779598129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3593010446350274372797505 2694757834762705779598129)
              ·
                refine ⟨2021068376072029334698597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694757834762705779598129 2021068376072029334698597)
                ·
                  refine ⟨378950320513505500255987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021068376072029334698597 378950320513505500255987)
                  ·
                    rfl

theorem cell22_3321014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_3321014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321014 prefixEnd_3321014 := by exact prefixLift 3321014
  have htrace : WordTrace (prefixWord ++ tailWord_3321014) baseStart_3321014 baseEnd_3321014 := by
    simpa [prefixWord, tailWord_3321014, baseEnd_3321014] using wordTrace_append hprefix tailTrace_3321014
  have hstable : (prefixWord ++ tailWord_3321014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321014).length < 2 ^ (prefixWord ++ tailWord_3321014).sum := by decide
  have hdescent : baseEnd_3321014 < baseStart_3321014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321023 : List Nat := [1, 1, 2, 2, 2, 2, 6, 2, 1, 3]
def baseStart_3321023 : Nat := 118140960795 + 3321023 * 2 ^ 59
def prefixEnd_3321023 : Nat := 4983230072969 + 3 ^ 40 * 3321023 * 2
def baseEnd_3321023 : Nat := 1136854042424443477292933

theorem tailTrace_3321023 : CollatzResearch.WordTrace tailWord_3321023 prefixEnd_3321023 1136854042424443477292933 := by
  unfold tailWord_3321023
  simp only [CollatzResearch.WordTrace]
  refine ⟨121127659847508331417559723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80751773231672220945039815 121127659847508331417559723)
  ·
    refine ⟨181691489771262497126339585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121127659847508331417559723 181691489771262497126339585)
    ·
      refine ⟨136268617328446872844754689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181691489771262497126339585 136268617328446872844754689)
      ·
        refine ⟨102201462996335154633566017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136268617328446872844754689 102201462996335154633566017)
        ·
          refine ⟨76651097247251365975174513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102201462996335154633566017 76651097247251365975174513)
          ·
            refine ⟨57488322935438524481380885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76651097247251365975174513 57488322935438524481380885)
            ·
              refine ⟨2694765137598680835064729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57488322935438524481380885 2694765137598680835064729)
              ·
                refine ⟨2021073853199010626298547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694765137598680835064729 2021073853199010626298547)
                ·
                  refine ⟨3031610779798515939447821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021073853199010626298547 3031610779798515939447821)
                  ·
                    refine ⟨1136854042424443477292933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031610779798515939447821 1136854042424443477292933)
                    ·
                      rfl

theorem cell22_3321023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 3].length) (baseStart_3321023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321023 prefixEnd_3321023 := by exact prefixLift 3321023
  have htrace : WordTrace (prefixWord ++ tailWord_3321023) baseStart_3321023 baseEnd_3321023 := by
    simpa [prefixWord, tailWord_3321023, baseEnd_3321023] using wordTrace_append hprefix tailTrace_3321023
  have hstable : (prefixWord ++ tailWord_3321023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321023).length < 2 ^ (prefixWord ++ tailWord_3321023).sum := by decide
  have hdescent : baseEnd_3321023 < baseStart_3321023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321034 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_3321034 : Nat := 118140960795 + 3321034 * 2 ^ 59
def prefixEnd_3321034 : Nat := 4983230072969 + 3 ^ 40 * 3321034 * 2
def baseEnd_3321034 : Nat := 1136857807949243115267899

theorem tailTrace_3321034 : CollatzResearch.WordTrace tailWord_3321034 prefixEnd_3321034 1136857807949243115267899 := by
  unfold tailWord_3321034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30282015262617120074052539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80752040700312320197473437 30282015262617120074052539)
  ·
    refine ⟨45423022893925680111078809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30282015262617120074052539 45423022893925680111078809)
    ·
      refine ⟨34067267170444260083309107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45423022893925680111078809 34067267170444260083309107)
      ·
        refine ⟨51100900755666390124963661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34067267170444260083309107 51100900755666390124963661)
        ·
          refine ⟨19162837783374896296861373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51100900755666390124963661 19162837783374896296861373)
          ·
            refine ⟨7186064168765586111323015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19162837783374896296861373 7186064168765586111323015)
            ·
              refine ⟨10779096253148379166984523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7186064168765586111323015 10779096253148379166984523)
              ·
                refine ⟨16168644379722568750476785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10779096253148379166984523 16168644379722568750476785)
                ·
                  refine ⟨12126483284791926562857589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16168644379722568750476785 12126483284791926562857589)
                  ·
                    refine ⟨1136857807949243115267899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12126483284791926562857589 1136857807949243115267899)
                    ·
                      rfl

theorem cell22_3321034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_3321034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321034 prefixEnd_3321034 := by exact prefixLift 3321034
  have htrace : WordTrace (prefixWord ++ tailWord_3321034) baseStart_3321034 baseEnd_3321034 := by
    simpa [prefixWord, tailWord_3321034, baseEnd_3321034] using wordTrace_append hprefix tailTrace_3321034
  have hstable : (prefixWord ++ tailWord_3321034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321034).length < 2 ^ (prefixWord ++ tailWord_3321034).sum := by decide
  have hdescent : baseEnd_3321034 < baseStart_3321034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321047 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 8]
def baseStart_3321047 : Nat := 118140960795 + 3321047 * 2 ^ 59
def prefixEnd_3321047 : Nat := 4983230072969 + 3 ^ 40 * 3321047 * 2
def baseEnd_3321047 : Nat := 378954086038305138230953

theorem tailTrace_3321047 : CollatzResearch.WordTrace tailWord_3321047 prefixEnd_3321047 378954086038305138230953 := by
  unfold tailWord_3321047
  simp only [CollatzResearch.WordTrace]
  refine ⟨121128535199421383516433395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80752356799614255677622263 121128535199421383516433395)
  ·
    refine ⟨181692802799132075274650093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121128535199421383516433395 181692802799132075274650093)
    ·
      refine ⟨68134801049674528227993785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181692802799132075274650093 68134801049674528227993785)
      ·
        refine ⟨51101100787255896170995339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68134801049674528227993785 51101100787255896170995339)
        ·
          refine ⟨76651651180883844256493009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51101100787255896170995339 76651651180883844256493009)
          ·
            refine ⟨57488738385662883192369757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76651651180883844256493009 57488738385662883192369757)
            ·
              refine ⟨21558276894623581197138659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57488738385662883192369757 21558276894623581197138659)
              ·
                refine ⟨32337415341935371795707989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21558276894623581197138659 32337415341935371795707989)
                ·
                  refine ⟨378954086038305138230953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32337415341935371795707989 378954086038305138230953)
                  ·
                    rfl

theorem cell22_3321047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 8].length) (baseStart_3321047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321047 prefixEnd_3321047 := by exact prefixLift 3321047
  have htrace : WordTrace (prefixWord ++ tailWord_3321047) baseStart_3321047 baseEnd_3321047 := by
    simpa [prefixWord, tailWord_3321047, baseEnd_3321047] using wordTrace_append hprefix tailTrace_3321047
  have hstable : (prefixWord ++ tailWord_3321047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321047).length < 2 ^ (prefixWord ++ tailWord_3321047).sum := by decide
  have hdescent : baseEnd_3321047 < baseStart_3321047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321049 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_3321049 : Nat := 118140960795 + 3321049 * 2 ^ 59
def prefixEnd_3321049 : Nat := 4983230072969 + 3 ^ 40 * 3321049 * 2
def baseEnd_3321049 : Nat := 1136862942755788076142853

theorem tailTrace_3321049 : CollatzResearch.WordTrace tailWord_3321049 prefixEnd_3321049 1136862942755788076142853 := by
  unfold tailWord_3321049
  simp only [CollatzResearch.WordTrace]
  refine ⟨121128608145414137858006201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80752405430276091905337467 121128608145414137858006201)
  ·
    refine ⟨90846456109060603393504651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121128608145414137858006201 90846456109060603393504651)
    ·
      refine ⟨136269684163590905090256977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90846456109060603393504651 136269684163590905090256977)
      ·
        refine ⟨102202263122693178817692733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136269684163590905090256977 102202263122693178817692733)
        ·
          refine ⟨38325848671009942056634775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102202263122693178817692733 38325848671009942056634775)
          ·
            refine ⟨57488773006514913084952163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38325848671009942056634775 57488773006514913084952163)
            ·
              refine ⟨86233159509772369627428245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57488773006514913084952163 86233159509772369627428245)
              ·
                refine ⟨4042179352020579826285699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86233159509772369627428245 4042179352020579826285699)
                ·
                  refine ⟨6063269028030869739428549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042179352020579826285699 6063269028030869739428549)
                  ·
                    refine ⟨1136862942755788076142853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6063269028030869739428549 1136862942755788076142853)
                    ·
                      rfl

theorem cell22_3321049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_3321049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321049 prefixEnd_3321049 := by exact prefixLift 3321049
  have htrace : WordTrace (prefixWord ++ tailWord_3321049) baseStart_3321049 baseEnd_3321049 := by
    simpa [prefixWord, tailWord_3321049, baseEnd_3321049] using wordTrace_append hprefix tailTrace_3321049
  have hstable : (prefixWord ++ tailWord_3321049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321049).length < 2 ^ (prefixWord ++ tailWord_3321049).sum := by decide
  have hdescent : baseEnd_3321049 < baseStart_3321049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321066 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_3321066 : Nat := 118140960795 + 3321066 * 2 ^ 59
def prefixEnd_3321066 : Nat := 4983230072969 + 3 ^ 40 * 3321066 * 2
def baseEnd_3321066 : Nat := 1136868762203205698467801

theorem tailTrace_3321066 : CollatzResearch.WordTrace tailWord_3321066 prefixEnd_3321066 1136868762203205698467801 := by
  unfold tailWord_3321066
  simp only [CollatzResearch.WordTrace]
  refine ⟨30282307046588137440343763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80752818790901699840916701 30282307046588137440343763)
  ·
    refine ⟨45423460569882206160515645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30282307046588137440343763 45423460569882206160515645)
    ·
      refine ⟨17033797713705827310193367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45423460569882206160515645 17033797713705827310193367)
      ·
        refine ⟨25550696570558740965290051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17033797713705827310193367 25550696570558740965290051)
        ·
          refine ⟨38326044855838111447935077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25550696570558740965290051 38326044855838111447935077)
          ·
            refine ⟨7186133410469645896487827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38326044855838111447935077 7186133410469645896487827)
            ·
              refine ⟨10779200115704468844731741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7186133410469645896487827 10779200115704468844731741)
              ·
                refine ⟨4042200043389175816774403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10779200115704468844731741 4042200043389175816774403)
                ·
                  refine ⟨6063300065083763725161605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042200043389175816774403 6063300065083763725161605)
                  ·
                    refine ⟨1136868762203205698467801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6063300065083763725161605 1136868762203205698467801)
                    ·
                      rfl

theorem cell22_3321066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_3321066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321066 prefixEnd_3321066 := by exact prefixLift 3321066
  have htrace : WordTrace (prefixWord ++ tailWord_3321066) baseStart_3321066 baseEnd_3321066 := by
    simpa [prefixWord, tailWord_3321066, baseEnd_3321066] using wordTrace_append hprefix tailTrace_3321066
  have hstable : (prefixWord ++ tailWord_3321066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321066).length < 2 ^ (prefixWord ++ tailWord_3321066).sum := by decide
  have hdescent : baseEnd_3321066 < baseStart_3321066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321079 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 4, 3]
def baseStart_3321079 : Nat := 118140960795 + 3321079 * 2 ^ 59
def prefixEnd_3321079 : Nat := 4983230072969 + 3 ^ 40 * 3321079 * 2
def baseEnd_3321079 : Nat := 1136873212368877997892761

theorem tailTrace_3321079 : CollatzResearch.WordTrace tailWord_3321079 prefixEnd_3321079 1136873212368877997892761 := by
  unfold tailWord_3321079
  simp only [CollatzResearch.WordTrace]
  refine ⟨121129702335305452981598291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80753134890203635321065527 121129702335305452981598291)
  ·
    refine ⟨181694553502958179472397437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121129702335305452981598291 181694553502958179472397437)
    ·
      refine ⟨68135457563609317302149039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181694553502958179472397437 68135457563609317302149039)
      ·
        refine ⟨102203186345413975953223559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68135457563609317302149039 102203186345413975953223559)
        ·
          refine ⟨153304779518120963929835339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102203186345413975953223559 153304779518120963929835339)
          ·
            refine ⟨229957169277181445894753009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153304779518120963929835339 229957169277181445894753009)
            ·
              refine ⟨172467876957886084421064757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229957169277181445894753009 172467876957886084421064757)
              ·
                refine ⟨16168863464801820414474821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172467876957886084421064757 16168863464801820414474821)
                ·
                  refine ⟨3031661899650341327714029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16168863464801820414474821 3031661899650341327714029)
                  ·
                    refine ⟨1136873212368877997892761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031661899650341327714029 1136873212368877997892761)
                    ·
                      rfl

theorem cell22_3321079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_3321079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321079 prefixEnd_3321079 := by exact prefixLift 3321079
  have htrace : WordTrace (prefixWord ++ tailWord_3321079) baseStart_3321079 baseEnd_3321079 := by
    simpa [prefixWord, tailWord_3321079, baseEnd_3321079] using wordTrace_append hprefix tailTrace_3321079
  have hstable : (prefixWord ++ tailWord_3321079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321079).length < 2 ^ (prefixWord ++ tailWord_3321079).sum := by decide
  have hdescent : baseEnd_3321079 < baseStart_3321079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321186 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3321186 : Nat := 118140960795 + 3321186 * 2 ^ 59
def prefixEnd_3321186 : Nat := 4983230072969 + 3 ^ 40 * 3321186 * 2
def baseEnd_3321186 : Nat := 1136909840655565385467433

theorem tailTrace_3321186 : CollatzResearch.WordTrace tailWord_3321186 prefixEnd_3321186 1136909840655565385467433 := by
  unfold tailWord_3321186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30283401236479452563935853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80755736630611873503828941 30283401236479452563935853)
  ·
    refine ⟨11356275463679794711475945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30283401236479452563935853 11356275463679794711475945)
    ·
      refine ⟨8517206597759846033606959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11356275463679794711475945 8517206597759846033606959)
      ·
        refine ⟨12775809896639769050410439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8517206597759846033606959 12775809896639769050410439)
        ·
          refine ⟨19163714844959653575615659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12775809896639769050410439 19163714844959653575615659)
          ·
            refine ⟨28745572267439480363423489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19163714844959653575615659 28745572267439480363423489)
            ·
              refine ⟨21559179200579610272567617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28745572267439480363423489 21559179200579610272567617)
              ·
                refine ⟨16169384400434707704425713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21559179200579610272567617 16169384400434707704425713)
                ·
                  refine ⟨12127038300326030778319285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16169384400434707704425713 12127038300326030778319285)
                  ·
                    refine ⟨1136909840655565385467433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12127038300326030778319285 1136909840655565385467433)
                    ·
                      rfl

theorem cell22_3321186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3321186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321186 prefixEnd_3321186 := by exact prefixLift 3321186
  have htrace : WordTrace (prefixWord ++ tailWord_3321186) baseStart_3321186 baseEnd_3321186 := by
    simpa [prefixWord, tailWord_3321186, baseEnd_3321186] using wordTrace_append hprefix tailTrace_3321186
  have hstable : (prefixWord ++ tailWord_3321186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321186).length < 2 ^ (prefixWord ++ tailWord_3321186).sum := by decide
  have hdescent : baseEnd_3321186 < baseStart_3321186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321199 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 6]
def baseStart_3321199 : Nat := 118140960795 + 3321199 * 2 ^ 59
def prefixEnd_3321199 : Nat := 4983230072969 + 3 ^ 40 * 3321199 * 2
def baseEnd_3321199 : Nat := 378971430273745894964131

theorem tailTrace_3321199 : CollatzResearch.WordTrace tailWord_3321199 prefixEnd_3321199 378971430273745894964131 := by
  unfold tailWord_3321199
  simp only [CollatzResearch.WordTrace]
  refine ⟨121134079094870713475966651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80756052729913808983977767 121134079094870713475966651)
  ·
    refine ⟨181701118642306070213949977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121134079094870713475966651 181701118642306070213949977)
    ·
      refine ⟨136275838981729552660462483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181701118642306070213949977 136275838981729552660462483)
      ·
        refine ⟨204413758472594328990693725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136275838981729552660462483 204413758472594328990693725)
        ·
          refine ⟨76655159427222873371510147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204413758472594328990693725 76655159427222873371510147)
          ·
            refine ⟨114982739140834310057265221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76655159427222873371510147 114982739140834310057265221)
            ·
              refine ⟨21559263588906433135737229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114982739140834310057265221 21559263588906433135737229)
              ·
                refine ⟨8084723845839912425901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21559263588906433135737229 8084723845839912425901461)
                ·
                  refine ⟨378971430273745894964131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8084723845839912425901461 378971430273745894964131)
                  ·
                    rfl

theorem cell22_3321199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 6].length) (baseStart_3321199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321199 prefixEnd_3321199 := by exact prefixLift 3321199
  have htrace : WordTrace (prefixWord ++ tailWord_3321199) baseStart_3321199 baseEnd_3321199 := by
    simpa [prefixWord, tailWord_3321199, baseEnd_3321199] using wordTrace_append hprefix tailTrace_3321199
  have hstable : (prefixWord ++ tailWord_3321199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321199).length < 2 ^ (prefixWord ++ tailWord_3321199).sum := by decide
  have hdescent : baseEnd_3321199 < baseStart_3321199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321265 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 2, 3]
def baseStart_3321265 : Nat := 118140960795 + 3321265 * 2 ^ 59
def prefixEnd_3321265 : Nat := 4983230072969 + 3 ^ 40 * 3321265 * 2
def baseEnd_3321265 : Nat := 1136936883970035512742191

theorem tailTrace_3321265 : CollatzResearch.WordTrace tailWord_3321265 prefixEnd_3321265 1136936883970035512742191 := by
  unfold tailWord_3321265
  simp only [CollatzResearch.WordTrace]
  refine ⟨121136486312631606747869249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80757657541754404498579499 121136486312631606747869249)
  ·
    refine ⟨90852364734473705060901937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121136486312631606747869249 90852364734473705060901937)
    ·
      refine ⟨68139273550855278795676453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90852364734473705060901937 68139273550855278795676453)
      ·
        refine ⟨12776113790785364774189335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68139273550855278795676453 12776113790785364774189335)
        ·
          refine ⟨19164170686178047161284003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12776113790785364774189335 19164170686178047161284003)
          ·
            refine ⟨28746256029267070741926005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19164170686178047161284003 28746256029267070741926005)
            ·
              refine ⟨2694961502743787882055563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28746256029267070741926005 2694961502743787882055563)
              ·
                refine ⟨4042442254115681823083345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694961502743787882055563 4042442254115681823083345)
                ·
                  refine ⟨3031831690586761367312509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042442254115681823083345 3031831690586761367312509)
                  ·
                    refine ⟨1136936883970035512742191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031831690586761367312509 1136936883970035512742191)
                    ·
                      rfl

theorem cell22_3321265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_3321265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321265 prefixEnd_3321265 := by exact prefixLift 3321265
  have htrace : WordTrace (prefixWord ++ tailWord_3321265) baseStart_3321265 baseEnd_3321265 := by
    simpa [prefixWord, tailWord_3321265, baseEnd_3321265] using wordTrace_append hprefix tailTrace_3321265
  have hstable : (prefixWord ++ tailWord_3321265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321265).length < 2 ^ (prefixWord ++ tailWord_3321265).sum := by decide
  have hdescent : baseEnd_3321265 < baseStart_3321265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321306 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_3321306 : Nat := 118140960795 + 3321306 * 2 ^ 59
def prefixEnd_3321306 : Nat := 4983230072969 + 3 ^ 40 * 3321306 * 2
def baseEnd_3321306 : Nat := 378983639702641690822355

theorem tailTrace_3321306 : CollatzResearch.WordTrace tailWord_3321306 prefixEnd_3321306 378983639702641690822355 := by
  unfold tailWord_3321306
  simp only [CollatzResearch.WordTrace]
  refine ⟨30284495426370767687527943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80758654470322047166741181 30284495426370767687527943)
  ·
    refine ⟨45426743139556151531291915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30284495426370767687527943 45426743139556151531291915)
    ·
      refine ⟨68140114709334227296937873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45426743139556151531291915 68140114709334227296937873)
      ·
        refine ⟨51105086032000670472703405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68140114709334227296937873 51105086032000670472703405)
        ·
          refine ⟨19164407262000251427263777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51105086032000670472703405 19164407262000251427263777)
          ·
            refine ⟨14373305446500188570447833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19164407262000251427263777 14373305446500188570447833)
            ·
              refine ⟨10779979084875141427835875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14373305446500188570447833 10779979084875141427835875)
              ·
                refine ⟨16169968627312712141753813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10779979084875141427835875 16169968627312712141753813)
                ·
                  refine ⟨378983639702641690822355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16169968627312712141753813 378983639702641690822355)
                  ·
                    rfl

theorem cell22_3321306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_3321306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321306 prefixEnd_3321306 := by exact prefixLift 3321306
  have htrace : WordTrace (prefixWord ++ tailWord_3321306) baseStart_3321306 baseEnd_3321306 := by
    simpa [prefixWord, tailWord_3321306, baseEnd_3321306] using wordTrace_append hprefix tailTrace_3321306
  have hstable : (prefixWord ++ tailWord_3321306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321306).length < 2 ^ (prefixWord ++ tailWord_3321306).sum := by decide
  have hdescent : baseEnd_3321306 < baseStart_3321306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321381 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3321381 : Nat := 118140960795 + 3321381 * 2 ^ 59
def prefixEnd_3321381 : Nat := 4983230072969 + 3 ^ 40 * 3321381 * 2
def baseEnd_3321381 : Nat := 1136976593140649876841835

theorem tailTrace_3321381 : CollatzResearch.WordTrace tailWord_3321381 prefixEnd_3321381 1136976593140649876841835 := by
  unfold tailWord_3321381
  simp only [CollatzResearch.WordTrace]
  refine ⟨121140717180211358559091997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80760478120140905706061331 121140717180211358559091997)
  ·
    refine ⟨45427768942579259459659499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121140717180211358559091997 45427768942579259459659499)
    ·
      refine ⟨68141653413868889189489249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45427768942579259459659499 68141653413868889189489249)
      ·
        refine ⟨51106240060401666892116937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68141653413868889189489249 51106240060401666892116937)
        ·
          refine ⟨38329680045301250169087703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51106240060401666892116937 38329680045301250169087703)
          ·
            refine ⟨57494520067951875253631555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38329680045301250169087703 57494520067951875253631555)
            ·
              refine ⟨86241780101927812880447333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57494520067951875253631555 86241780101927812880447333)
              ·
                refine ⟨16170333769111464915083875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86241780101927812880447333 16170333769111464915083875)
                ·
                  refine ⟨24255500653667197372625813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16170333769111464915083875 24255500653667197372625813)
                  ·
                    refine ⟨1136976593140649876841835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24255500653667197372625813 1136976593140649876841835)
                    ·
                      rfl

theorem cell22_3321381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3321381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321381 prefixEnd_3321381 := by exact prefixLift 3321381
  have htrace : WordTrace (prefixWord ++ tailWord_3321381) baseStart_3321381 baseEnd_3321381 := by
    simpa [prefixWord, tailWord_3321381, baseEnd_3321381] using wordTrace_append hprefix tailTrace_3321381
  have hstable : (prefixWord ++ tailWord_3321381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321381).length < 2 ^ (prefixWord ++ tailWord_3321381).sum := by decide
  have hdescent : baseEnd_3321381 < baseStart_3321381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321404 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_3321404 : Nat := 118140960795 + 3321404 * 2 ^ 59
def prefixEnd_3321404 : Nat := 4983230072969 + 3 ^ 40 * 3321404 * 2
def baseEnd_3321404 : Nat := 1136984466510685483516765

theorem tailTrace_3321404 : CollatzResearch.WordTrace tailWord_3321404 prefixEnd_3321404 1136984466510685483516765 := by
  unfold tailWord_3321404
  simp only [CollatzResearch.WordTrace]
  refine ⟨60570778029564016743589633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80761037372752022324786177 60570778029564016743589633)
  ·
    refine ⟨45428083522173012557692225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60570778029564016743589633 45428083522173012557692225)
    ·
      refine ⟨34071062641629759418269169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45428083522173012557692225 34071062641629759418269169)
      ·
        refine ⟨25553296981222319563701877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34071062641629759418269169 25553296981222319563701877)
        ·
          refine ⟨2395621591989592459097051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25553296981222319563701877 2395621591989592459097051)
          ·
            refine ⟨3593432387984388688645577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395621591989592459097051 3593432387984388688645577)
            ·
              refine ⟨2695074290988291516484183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3593432387984388688645577 2695074290988291516484183)
              ·
                refine ⟨4042611436482437274726275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695074290988291516484183 4042611436482437274726275)
                ·
                  refine ⟨6063917154723655912089413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042611436482437274726275 6063917154723655912089413)
                  ·
                    refine ⟨1136984466510685483516765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6063917154723655912089413 1136984466510685483516765)
                    ·
                      rfl

theorem cell22_3321404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_3321404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321404 prefixEnd_3321404 := by exact prefixLift 3321404
  have htrace : WordTrace (prefixWord ++ tailWord_3321404) baseStart_3321404 baseEnd_3321404 := by
    simpa [prefixWord, tailWord_3321404, baseEnd_3321404] using wordTrace_append hprefix tailTrace_3321404
  have hstable : (prefixWord ++ tailWord_3321404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321404).length < 2 ^ (prefixWord ++ tailWord_3321404).sum := by decide
  have hdescent : baseEnd_3321404 < baseStart_3321404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321445 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_3321445 : Nat := 118140960795 + 3321445 * 2 ^ 59
def prefixEnd_3321445 : Nat := 4983230072969 + 3 ^ 40 * 3321445 * 2
def baseEnd_3321445 : Nat := 1136998501648575043241639

theorem tailTrace_3321445 : CollatzResearch.WordTrace tailWord_3321445 prefixEnd_3321445 1136998501648575043241639 := by
  unfold tailWord_3321445
  simp only [CollatzResearch.WordTrace]
  refine ⟨121143051451979497489421789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80762034301319664992947859 121143051451979497489421789)
  ·
    refine ⟨45428644294492311558533171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121143051451979497489421789 45428644294492311558533171)
    ·
      refine ⟨68142966441738467337799757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45428644294492311558533171 68142966441738467337799757)
      ·
        refine ⟨25553612415651925251674909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68142966441738467337799757 25553612415651925251674909)
        ·
          refine ⟨9582604655869471969378091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25553612415651925251674909 9582604655869471969378091)
          ·
            refine ⟨14373906983804207954067137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9582604655869471969378091 14373906983804207954067137)
            ·
              refine ⟨10780430237853155965550353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14373906983804207954067137 10780430237853155965550353)
              ·
                refine ⟨8085322678389866974162765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10780430237853155965550353 8085322678389866974162765)
                ·
                  refine ⟨3031996004396200115311037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8085322678389866974162765 3031996004396200115311037)
                  ·
                    refine ⟨1136998501648575043241639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3031996004396200115311037 1136998501648575043241639)
                    ·
                      rfl

theorem cell22_3321445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_3321445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321445 prefixEnd_3321445 := by exact prefixLift 3321445
  have htrace : WordTrace (prefixWord ++ tailWord_3321445) baseStart_3321445 baseEnd_3321445 := by
    simpa [prefixWord, tailWord_3321445, baseEnd_3321445] using wordTrace_append hprefix tailTrace_3321445
  have hstable : (prefixWord ++ tailWord_3321445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321445).length < 2 ^ (prefixWord ++ tailWord_3321445).sum := by decide
  have hdescent : baseEnd_3321445 < baseStart_3321445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321458 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_3321458 : Nat := 118140960795 + 3321458 * 2 ^ 59
def prefixEnd_3321458 : Nat := 4983230072969 + 3 ^ 40 * 3321458 * 2
def baseEnd_3321458 : Nat := 379000983938082447555533

theorem tailTrace_3321458 : CollatzResearch.WordTrace tailWord_3321458 prefixEnd_3321458 379000983938082447555533 := by
  unfold tailWord_3321458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30285881400233100177411257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80762350400621600473096685 30285881400233100177411257)
  ·
    refine ⟨22714411050174825133058443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30285881400233100177411257 22714411050174825133058443)
    ·
      refine ⟨34071616575262237699587665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22714411050174825133058443 34071616575262237699587665)
      ·
        refine ⟨25553712431446678274690749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34071616575262237699587665 25553712431446678274690749)
        ·
          refine ⟨9582642161792504353009031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25553712431446678274690749 9582642161792504353009031)
          ·
            refine ⟨14373963242688756529513547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9582642161792504353009031 14373963242688756529513547)
            ·
              refine ⟨21560944864033134794270321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14373963242688756529513547 21560944864033134794270321)
              ·
                refine ⟨16170708648024851095702741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21560944864033134794270321 16170708648024851095702741)
                ·
                  refine ⟨379000983938082447555533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16170708648024851095702741 379000983938082447555533)
                  ·
                    rfl

theorem cell22_3321458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_3321458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321458 prefixEnd_3321458 := by exact prefixLift 3321458
  have htrace : WordTrace (prefixWord ++ tailWord_3321458) baseStart_3321458 baseEnd_3321458 := by
    simpa [prefixWord, tailWord_3321458, baseEnd_3321458] using wordTrace_append hprefix tailTrace_3321458
  have hstable : (prefixWord ++ tailWord_3321458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321458).length < 2 ^ (prefixWord ++ tailWord_3321458).sum := by decide
  have hdescent : baseEnd_3321458 < baseStart_3321458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321471 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 10]
def baseStart_3321471 : Nat := 118140960795 + 3321471 * 2 ^ 59
def prefixEnd_3321471 : Nat := 4983230072969 + 3 ^ 40 * 3321471 * 2
def baseEnd_3321471 : Nat := 1137007401979919642091559

theorem tailTrace_3321471 : CollatzResearch.WordTrace tailWord_3321471 prefixEnd_3321471 1137007401979919642091559 := by
  unfold tailWord_3321471
  simp only [CollatzResearch.WordTrace]
  refine ⟨121143999749885303929868267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80762666499923535953245511 121143999749885303929868267)
  ·
    refine ⟨181715999624827955894802401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121143999749885303929868267 181715999624827955894802401)
    ·
      refine ⟨136286999718620966921101801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181715999624827955894802401 136286999718620966921101801)
      ·
        refine ⟨102215249788965725190826351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136286999718620966921101801 102215249788965725190826351)
        ·
          refine ⟨153322874683448587786239527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102215249788965725190826351 153322874683448587786239527)
          ·
            refine ⟨229984312025172881679359291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153322874683448587786239527 229984312025172881679359291)
            ·
              refine ⟨344976468037759322519038937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229984312025172881679359291 344976468037759322519038937)
              ·
                refine ⟨258732351028319491889279203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344976468037759322519038937 258732351028319491889279203)
                ·
                  refine ⟨388098526542479237833918805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258732351028319491889279203 388098526542479237833918805)
                  ·
                    refine ⟨1137007401979919642091559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 388098526542479237833918805 1137007401979919642091559)
                    ·
                      rfl

theorem cell22_3321471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_3321471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321471 prefixEnd_3321471 := by exact prefixLift 3321471
  have htrace : WordTrace (prefixWord ++ tailWord_3321471) baseStart_3321471 baseEnd_3321471 := by
    simpa [prefixWord, tailWord_3321471, baseEnd_3321471] using wordTrace_append hprefix tailTrace_3321471
  have hstable : (prefixWord ++ tailWord_3321471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321471).length < 2 ^ (prefixWord ++ tailWord_3321471).sum := by decide
  have hdescent : baseEnd_3321471 < baseStart_3321471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321479 : List Nat := [1, 1, 4, 2, 1, 4, 3, 2, 1, 3]
def baseStart_3321479 : Nat := 118140960795 + 3321479 * 2 ^ 59
def prefixEnd_3321479 : Nat := 4983230072969 + 3 ^ 40 * 3321479 * 2
def baseEnd_3321479 : Nat := 1137010140543410287891535

theorem tailTrace_3321479 : CollatzResearch.WordTrace tailWord_3321479 prefixEnd_3321479 1137010140543410287891535 := by
  unfold tailWord_3321479
  simp only [CollatzResearch.WordTrace]
  refine ⟨121144291533856321296159491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80762861022570880864106327 121144291533856321296159491)
  ·
    refine ⟨181716437300784481944239237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121144291533856321296159491 181716437300784481944239237)
    ·
      refine ⟨34071831993897090364544857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181716437300784481944239237 34071831993897090364544857)
      ·
        refine ⟨25553873995422817773408643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34071831993897090364544857 25553873995422817773408643)
        ·
          refine ⟨38330810993134226660112965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25553873995422817773408643 38330810993134226660112965)
          ·
            refine ⟨7187027061212667498771181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38330810993134226660112965 7187027061212667498771181)
            ·
              refine ⟨2695135147954750312039193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7187027061212667498771181 2695135147954750312039193)
              ·
                refine ⟨2021351360966062734029395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695135147954750312039193 2021351360966062734029395)
                ·
                  refine ⟨3032027041449094101044093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021351360966062734029395 3032027041449094101044093)
                  ·
                    refine ⟨1137010140543410287891535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3032027041449094101044093 1137010140543410287891535)
                    ·
                      rfl

theorem cell22_3321479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_3321479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321479 prefixEnd_3321479 := by exact prefixLift 3321479
  have htrace : WordTrace (prefixWord ++ tailWord_3321479) baseStart_3321479 baseEnd_3321479 := by
    simpa [prefixWord, tailWord_3321479, baseEnd_3321479] using wordTrace_append hprefix tailTrace_3321479
  have hstable : (prefixWord ++ tailWord_3321479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321479).length < 2 ^ (prefixWord ++ tailWord_3321479).sum := by decide
  have hdescent : baseEnd_3321479 < baseStart_3321479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321492 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3321492 : Nat := 118140960795 + 3321492 * 2 ^ 59
def prefixEnd_3321492 : Nat := 4983230072969 + 3 ^ 40 * 3321492 * 2
def baseEnd_3321492 : Nat := 379004863569694195772165

theorem tailTrace_3321492 : CollatzResearch.WordTrace tailWord_3321492 prefixEnd_3321492 379004863569694195772165 := by
  unfold tailWord_3321492
  simp only [CollatzResearch.WordTrace]
  refine ⟨60572382841404612258191365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80763177121872816344255153 60572382841404612258191365)
  ·
    refine ⟨11357321782763364798410881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60572382841404612258191365 11357321782763364798410881)
    ·
      refine ⟨8517991337072523598808161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11357321782763364798410881 8517991337072523598808161)
      ·
        refine ⟨6388493502804392699106121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8517991337072523598808161 6388493502804392699106121)
        ·
          refine ⟨4791370127103294524329591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6388493502804392699106121 4791370127103294524329591)
          ·
            refine ⟨7187055190654941786494387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791370127103294524329591 7187055190654941786494387)
            ·
              refine ⟨10780582785982412679741581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187055190654941786494387 10780582785982412679741581)
              ·
                refine ⟨4042718544743404754903093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10780582785982412679741581 4042718544743404754903093)
                ·
                  refine ⟨379004863569694195772165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4042718544743404754903093 379004863569694195772165)
                  ·
                    rfl

theorem cell22_3321492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3321492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321492 prefixEnd_3321492 := by exact prefixLift 3321492
  have htrace : WordTrace (prefixWord ++ tailWord_3321492) baseStart_3321492 baseEnd_3321492 := by
    simpa [prefixWord, tailWord_3321492, baseEnd_3321492] using wordTrace_append hprefix tailTrace_3321492
  have hstable : (prefixWord ++ tailWord_3321492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321492).length < 2 ^ (prefixWord ++ tailWord_3321492).sum := by decide
  have hdescent : baseEnd_3321492 < baseStart_3321492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321505 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3321505 : Nat := 118140960795 + 3321505 * 2 ^ 59
def prefixEnd_3321505 : Nat := 4983230072969 + 3 ^ 40 * 3321505 * 2
def baseEnd_3321505 : Nat := 1137019040874754886741455

theorem tailTrace_3321505 : CollatzResearch.WordTrace tailWord_3321505 prefixEnd_3321505 1137019040874754886741455 := by
  unfold tailWord_3321505
  simp only [CollatzResearch.WordTrace]
  refine ⟨121145239831762127736605969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80763493221174751824403979 121145239831762127736605969)
  ·
    refine ⟨90858929873821595802454477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121145239831762127736605969 90858929873821595802454477)
    ·
      refine ⟨34072098702683098425920429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90858929873821595802454477 34072098702683098425920429)
      ·
        refine ⟨12777037013506161909720161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34072098702683098425920429 12777037013506161909720161)
        ·
          refine ⟨9582777760129621432290121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12777037013506161909720161 9582777760129621432290121)
          ·
            refine ⟨7187083320097216074217591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9582777760129621432290121 7187083320097216074217591)
            ·
              refine ⟨10780624980145824111326387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187083320097216074217591 10780624980145824111326387)
              ·
                refine ⟨16170937470218736166989581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10780624980145824111326387 16170937470218736166989581)
                ·
                  refine ⟨6064101551332026062621093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16170937470218736166989581 6064101551332026062621093)
                  ·
                    refine ⟨1137019040874754886741455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6064101551332026062621093 1137019040874754886741455)
                    ·
                      rfl

theorem cell22_3321505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3321505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321505 prefixEnd_3321505 := by exact prefixLift 3321505
  have htrace : WordTrace (prefixWord ++ tailWord_3321505) baseStart_3321505 baseEnd_3321505 := by
    simpa [prefixWord, tailWord_3321505, baseEnd_3321505] using wordTrace_append hprefix tailTrace_3321505
  have hstable : (prefixWord ++ tailWord_3321505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321505).length < 2 ^ (prefixWord ++ tailWord_3321505).sum := by decide
  have hdescent : baseEnd_3321505 < baseStart_3321505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321687 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 1, 5]
def baseStart_3321687 : Nat := 118140960795 + 3321687 * 2 ^ 59
def prefixEnd_3321687 : Nat := 4983230072969 + 3 ^ 40 * 3321687 * 2
def baseEnd_3321687 : Nat := 1137081343194167078690897

theorem tailTrace_3321687 : CollatzResearch.WordTrace tailWord_3321687 prefixEnd_3321687 1137081343194167078690897 := by
  unfold tailWord_3321687
  simp only [CollatzResearch.WordTrace]
  refine ⟨121151877917102772819731315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80767918611401848546487543 121151877917102772819731315)
  ·
    refine ⟨181727816875654159229596973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121151877917102772819731315 181727816875654159229596973)
    ·
      refine ⟨68147931328370309711098865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181727816875654159229596973 68147931328370309711098865)
      ·
        refine ⟨51110948496277732283324149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68147931328370309711098865 51110948496277732283324149)
        ·
          refine ⟨4791651421526037401561639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51110948496277732283324149 4791651421526037401561639)
          ·
            refine ⟨7187477132289056102342459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791651421526037401561639 7187477132289056102342459)
            ·
              refine ⟨10781215698433584153513689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187477132289056102342459 10781215698433584153513689)
              ·
                refine ⟨8085911773825188115135267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10781215698433584153513689 8085911773825188115135267)
                ·
                  refine ⟨12128867660737782172702901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8085911773825188115135267 12128867660737782172702901)
                  ·
                    refine ⟨1137081343194167078690897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12128867660737782172702901 1137081343194167078690897)
                    ·
                      rfl

theorem cell22_3321687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_3321687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321687 prefixEnd_3321687 := by exact prefixLift 3321687
  have htrace : WordTrace (prefixWord ++ tailWord_3321687) baseStart_3321687 baseEnd_3321687 := by
    simpa [prefixWord, tailWord_3321687, baseEnd_3321687] using wordTrace_append hprefix tailTrace_3321687
  have hstable : (prefixWord ++ tailWord_3321687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321687).length < 2 ^ (prefixWord ++ tailWord_3321687).sum := by decide
  have hdescent : baseEnd_3321687 < baseStart_3321687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321700 : List Nat := [2, 3, 1, 1, 5, 10]
def baseStart_3321700 : Nat := 118140960795 + 3321700 * 2 ^ 59
def prefixEnd_3321700 : Nat := 4983230072969 + 3 ^ 40 * 3321700 * 2
def baseEnd_3321700 : Nat := 14038096214319004668097

theorem tailTrace_3321700 : CollatzResearch.WordTrace tailWord_3321700 prefixEnd_3321700 14038096214319004668097 := by
  unfold tailWord_3321700
  simp only [CollatzResearch.WordTrace]
  refine ⟨60576176033027838019977277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80768234710703784026636369 60576176033027838019977277)
  ·
    refine ⟨22716066012385439257491479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60576176033027838019977277 22716066012385439257491479)
    ·
      refine ⟨34074099018578158886237219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22716066012385439257491479 34074099018578158886237219)
      ·
        refine ⟨51111148527867238329355829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34074099018578158886237219 51111148527867238329355829)
        ·
          refine ⟨4791670174487553593377109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51111148527867238329355829 4791670174487553593377109)
          ·
            refine ⟨14038096214319004668097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4791670174487553593377109 14038096214319004668097)
            ·
              rfl

theorem cell22_3321700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 10].length) (baseStart_3321700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321700 prefixEnd_3321700 := by exact prefixLift 3321700
  have htrace : WordTrace (prefixWord ++ tailWord_3321700) baseStart_3321700 baseEnd_3321700 := by
    simpa [prefixWord, tailWord_3321700, baseEnd_3321700] using wordTrace_append hprefix tailTrace_3321700
  have hstable : (prefixWord ++ tailWord_3321700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321700).length < 2 ^ (prefixWord ++ tailWord_3321700).sum := by decide
  have hdescent : baseEnd_3321700 < baseStart_3321700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321704 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 2, 3]
def baseStart_3321704 : Nat := 118140960795 + 3321704 * 2 ^ 59
def prefixEnd_3321704 : Nat := 4983230072969 + 3 ^ 40 * 3321704 * 2
def baseEnd_3321704 : Nat := 1137087162641584701015845

theorem tailTrace_3321704 : CollatzResearch.WordTrace tailWord_3321704 prefixEnd_3321704 1137087162641584701015845 := by
  unfold tailWord_3321704
  simp only [CollatzResearch.WordTrace]
  refine ⟨60576248979020592361550083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80768331972027456482066777 60576248979020592361550083)
  ·
    refine ⟨90864373468530888542325125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60576248979020592361550083 90864373468530888542325125)
    ·
      refine ⟨17037070025349541601685961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90864373468530888542325125 17037070025349541601685961)
      ·
        refine ⟨12777802519012156201264471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17037070025349541601685961 12777802519012156201264471)
        ·
          refine ⟨19166703778518234301896707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12777802519012156201264471 19166703778518234301896707)
          ·
            refine ⟨28750055667777351452845061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19166703778518234301896707 28750055667777351452845061)
            ·
              refine ⟨5390635437708253397408449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28750055667777351452845061 5390635437708253397408449)
              ·
                refine ⟨4042976578281190048056337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5390635437708253397408449 4042976578281190048056337)
                ·
                  refine ⟨3032232433710892536042253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042976578281190048056337 3032232433710892536042253)
                  ·
                    refine ⟨1137087162641584701015845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3032232433710892536042253 1137087162641584701015845)
                    ·
                      rfl

theorem cell22_3321704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_3321704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321704 prefixEnd_3321704 := by exact prefixLift 3321704
  have htrace : WordTrace (prefixWord ++ tailWord_3321704) baseStart_3321704 baseEnd_3321704 := by
    simpa [prefixWord, tailWord_3321704, baseEnd_3321704] using wordTrace_append hprefix tailTrace_3321704
  have hstable : (prefixWord ++ tailWord_3321704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321704).length < 2 ^ (prefixWord ++ tailWord_3321704).sum := by decide
  have hdescent : baseEnd_3321704 < baseStart_3321704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321706 : List Nat := [3, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_3321706 : Nat := 118140960795 + 3321706 * 2 ^ 59
def prefixEnd_3321706 : Nat := 4983230072969 + 3 ^ 40 * 3321706 * 2
def baseEnd_3321706 : Nat := 379029282427485787488613

theorem tailTrace_3321706 : CollatzResearch.WordTrace tailWord_3321706 prefixEnd_3321706 379029282427485787488613 := by
  unfold tailWord_3321706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288142726008484766168243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80768380602689292709781981 30288142726008484766168243)
  ·
    refine ⟨45432214089012727149252365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30288142726008484766168243 45432214089012727149252365)
    ·
      refine ⟨17037080283379772680969637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45432214089012727149252365 17037080283379772680969637)
      ·
        refine ⟨3194452553133707377681807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17037080283379772680969637 3194452553133707377681807)
        ·
          refine ⟨4791678829700561066522711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3194452553133707377681807 4791678829700561066522711)
          ·
            refine ⟨7187518244550841599784067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791678829700561066522711 7187518244550841599784067)
            ·
              refine ⟨10781277366826262399676101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187518244550841599784067 10781277366826262399676101)
              ·
                refine ⟨2021489506279924199939269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10781277366826262399676101 2021489506279924199939269)
                ·
                  refine ⟨379029282427485787488613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021489506279924199939269 379029282427485787488613)
                  ·
                    rfl

theorem cell22_3321706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_3321706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321706 prefixEnd_3321706 := by exact prefixLift 3321706
  have htrace : WordTrace (prefixWord ++ tailWord_3321706) baseStart_3321706 baseEnd_3321706 := by
    simpa [prefixWord, tailWord_3321706, baseEnd_3321706] using wordTrace_append hprefix tailTrace_3321706
  have hstable : (prefixWord ++ tailWord_3321706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321706).length < 2 ^ (prefixWord ++ tailWord_3321706).sum := by decide
  have hdescent : baseEnd_3321706 < baseStart_3321706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321732 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_3321732 : Nat := 118140960795 + 3321732 * 2 ^ 59
def prefixEnd_3321732 : Nat := 4983230072969 + 3 ^ 40 * 3321732 * 2
def baseEnd_3321732 : Nat := 1137096747613801961315759

theorem tailTrace_3321732 : CollatzResearch.WordTrace tailWord_3321732 prefixEnd_3321732 1137096747613801961315759 := by
  unfold tailWord_3321732
  simp only [CollatzResearch.WordTrace]
  refine ⟨60576759600969872752559725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80769012801293163670079633 60576759600969872752559725)
  ·
    refine ⟨22716284850363702282209897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60576759600969872752559725 22716284850363702282209897)
    ·
      refine ⟨17037213637772776711657423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22716284850363702282209897 17037213637772776711657423)
      ·
        refine ⟨25555820456659165067486135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17037213637772776711657423 25555820456659165067486135)
        ·
          refine ⟨38333730684988747601229203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25555820456659165067486135 38333730684988747601229203)
          ·
            refine ⟨57500596027483121401843805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38333730684988747601229203 57500596027483121401843805)
            ·
              refine ⟨21562723510306170525691427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57500596027483121401843805 21562723510306170525691427)
              ·
                refine ⟨32344085265459255788537141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21562723510306170525691427 32344085265459255788537141)
                ·
                  refine ⟨3032257993636805230175357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32344085265459255788537141 3032257993636805230175357)
                  ·
                    refine ⟨1137096747613801961315759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3032257993636805230175357 1137096747613801961315759)
                    ·
                      rfl

theorem cell22_3321732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_3321732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321732 prefixEnd_3321732 := by exact prefixLift 3321732
  have htrace : WordTrace (prefixWord ++ tailWord_3321732) baseStart_3321732 baseEnd_3321732 := by
    simpa [prefixWord, tailWord_3321732, baseEnd_3321732] using wordTrace_append hprefix tailTrace_3321732
  have hstable : (prefixWord ++ tailWord_3321732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321732).length < 2 ^ (prefixWord ++ tailWord_3321732).sum := by decide
  have hdescent : baseEnd_3321732 < baseStart_3321732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321736 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 2, 4]
def baseStart_3321736 : Nat := 118140960795 + 3321736 * 2 ^ 59
def prefixEnd_3321736 : Nat := 4983230072969 + 3 ^ 40 * 3321736 * 2
def baseEnd_3321736 : Nat := 1137098116895547284215747

theorem tailTrace_3321736 : CollatzResearch.WordTrace tailWord_3321736 prefixEnd_3321736 1137098116895547284215747 := by
  unfold tailWord_3321736
  simp only [CollatzResearch.WordTrace]
  refine ⟨60576832546962627094132531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80769110062616836125510041 60576832546962627094132531)
  ·
    refine ⟨90865248820443940641198797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60576832546962627094132531 90865248820443940641198797)
    ·
      refine ⟨34074468307666477740449549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90865248820443940641198797 34074468307666477740449549)
      ·
        refine ⟨12777925615374929152668581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34074468307666477740449549 12777925615374929152668581)
        ·
          refine ⟨2395861052882799216125359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12777925615374929152668581 2395861052882799216125359)
          ·
            refine ⟨3593791579324198824188039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395861052882799216125359 3593791579324198824188039)
            ·
              refine ⟨5390687368986298236282059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593791579324198824188039 5390687368986298236282059)
              ·
                refine ⟨8086031053479447354423089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5390687368986298236282059 8086031053479447354423089)
                ·
                  refine ⟨6064523290109585515817317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086031053479447354423089 6064523290109585515817317)
                  ·
                    refine ⟨1137098116895547284215747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6064523290109585515817317 1137098116895547284215747)
                    ·
                      rfl

theorem cell22_3321736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_3321736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321736 prefixEnd_3321736 := by exact prefixLift 3321736
  have htrace : WordTrace (prefixWord ++ tailWord_3321736) baseStart_3321736 baseEnd_3321736 := by
    simpa [prefixWord, tailWord_3321736, baseEnd_3321736] using wordTrace_append hprefix tailTrace_3321736
  have hstable : (prefixWord ++ tailWord_3321736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321736).length < 2 ^ (prefixWord ++ tailWord_3321736).sum := by decide
  have hdescent : baseEnd_3321736 < baseStart_3321736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321777 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_3321777 : Nat := 118140960795 + 3321777 * 2 ^ 59
def prefixEnd_3321777 : Nat := 4983230072969 + 3 ^ 40 * 3321777 * 2
def baseEnd_3321777 : Nat := 1137112152033436843940621

theorem tailTrace_3321777 : CollatzResearch.WordTrace tailWord_3321777 prefixEnd_3321777 1137112152033436843940621 := by
  unfold tailWord_3321777
  simp only [CollatzResearch.WordTrace]
  refine ⟨121155160486776718190507585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80770106991184478793671723 121155160486776718190507585)
  ·
    refine ⟨90866370365082538642880689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121155160486776718190507585 90866370365082538642880689)
    ·
      refine ⟨68149777773811903982160517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90866370365082538642880689 68149777773811903982160517)
      ·
        refine ⟨12778083332589731996655097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68149777773811903982160517 12778083332589731996655097)
        ·
          refine ⟨9583562499442298997491323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12778083332589731996655097 9583562499442298997491323)
          ·
            refine ⟨14375343749163448496236985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9583562499442298997491323 14375343749163448496236985)
            ·
              refine ⟨10781507811872586372177739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14375343749163448496236985 10781507811872586372177739)
              ·
                refine ⟨16172261717808879558266609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10781507811872586372177739 16172261717808879558266609)
                ·
                  refine ⟨12129196288356659668699957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16172261717808879558266609 12129196288356659668699957)
                  ·
                    refine ⟨1137112152033436843940621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12129196288356659668699957 1137112152033436843940621)
                    ·
                      rfl

theorem cell22_3321777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_3321777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321777 prefixEnd_3321777 := by exact prefixLift 3321777
  have htrace : WordTrace (prefixWord ++ tailWord_3321777) baseStart_3321777 baseEnd_3321777 := by
    simpa [prefixWord, tailWord_3321777, baseEnd_3321777] using wordTrace_append hprefix tailTrace_3321777
  have hstable : (prefixWord ++ tailWord_3321777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321777).length < 2 ^ (prefixWord ++ tailWord_3321777).sum := by decide
  have hdescent : baseEnd_3321777 < baseStart_3321777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321839 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 2, 3]
def baseStart_3321839 : Nat := 118140960795 + 3321839 * 2 ^ 59
def prefixEnd_3321839 : Nat := 4983230072969 + 3 ^ 40 * 3321839 * 2
def baseEnd_3321839 : Nat := 1137133375900489348890431

theorem tailTrace_3321839 : CollatzResearch.WordTrace tailWord_3321839 prefixEnd_3321839 1137133375900489348890431 := by
  unfold tailWord_3321839
  simp only [CollatzResearch.WordTrace]
  refine ⟨121157421812552102779264571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80771614541701401852843047 121157421812552102779264571)
  ·
    refine ⟨181736132718828154168896857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121157421812552102779264571 181736132718828154168896857)
    ·
      refine ⟨136302099539121115626672643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181736132718828154168896857 136302099539121115626672643)
      ·
        refine ⟨204453149308681673440008965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136302099539121115626672643 204453149308681673440008965)
        ·
          refine ⟨38334965495377813770001681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204453149308681673440008965 38334965495377813770001681)
          ·
            refine ⟨28751224121533360327501261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38334965495377813770001681 28751224121533360327501261)
            ·
              refine ⟨10781709045575010122812973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28751224121533360327501261 10781709045575010122812973)
              ·
                refine ⟨4043140892090628796054865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10781709045575010122812973 4043140892090628796054865)
                ·
                  refine ⟨3032355669067971597041149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043140892090628796054865 3032355669067971597041149)
                  ·
                    refine ⟨1137133375900489348890431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3032355669067971597041149 1137133375900489348890431)
                    ·
                      rfl

theorem cell22_3321839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_3321839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321839 prefixEnd_3321839 := by exact prefixLift 3321839
  have htrace : WordTrace (prefixWord ++ tailWord_3321839) baseStart_3321839 baseEnd_3321839 := by
    simpa [prefixWord, tailWord_3321839, baseEnd_3321839] using wordTrace_append hprefix tailTrace_3321839
  have hstable : (prefixWord ++ tailWord_3321839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321839).length < 2 ^ (prefixWord ++ tailWord_3321839).sum := by decide
  have hdescent : baseEnd_3321839 < baseStart_3321839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321882 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_3321882 : Nat := 118140960795 + 3321882 * 2 ^ 59
def prefixEnd_3321882 : Nat := 4983230072969 + 3 ^ 40 * 3321882 * 2
def baseEnd_3321882 : Nat := 1137148095679251570065299

theorem tailTrace_3321882 : CollatzResearch.WordTrace tailWord_3321882 prefixEnd_3321882 1137148095679251570065299 := by
  unfold tailWord_3321882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30289747537849080280769975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80772660100930880748719933 30289747537849080280769975)
  ·
    refine ⟨45434621306773620421154963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30289747537849080280769975 45434621306773620421154963)
    ·
      refine ⟨68151931960160430631732445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45434621306773620421154963 68151931960160430631732445)
      ·
        refine ⟨25556974485060161486899667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68151931960160430631732445 25556974485060161486899667)
        ·
          refine ⟨38335461727590242230349501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25556974485060161486899667 38335461727590242230349501)
          ·
            refine ⟨14375798147846340836381063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38335461727590242230349501 14375798147846340836381063)
            ·
              refine ⟨21563697221769511254571595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14375798147846340836381063 21563697221769511254571595)
              ·
                refine ⟨32345545832654266881857393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21563697221769511254571595 32345545832654266881857393)
                ·
                  refine ⟨24259159374490700161393045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32345545832654266881857393 24259159374490700161393045)
                  ·
                    refine ⟨1137148095679251570065299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24259159374490700161393045 1137148095679251570065299)
                    ·
                      rfl

theorem cell22_3321882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_3321882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321882 prefixEnd_3321882 := by exact prefixLift 3321882
  have htrace : WordTrace (prefixWord ++ tailWord_3321882) baseStart_3321882 baseEnd_3321882 := by
    simpa [prefixWord, tailWord_3321882, baseEnd_3321882] using wordTrace_append hprefix tailTrace_3321882
  have hstable : (prefixWord ++ tailWord_3321882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321882).length < 2 ^ (prefixWord ++ tailWord_3321882).sum := by decide
  have hdescent : baseEnd_3321882 < baseStart_3321882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321987 : List Nat := [1, 1, 1, 3, 3, 3, 10]
def baseStart_3321987 : Nat := 118140960795 + 3321987 * 2 ^ 59
def prefixEnd_3321987 : Nat := 4983230072969 + 3 ^ 40 * 3321987 * 2
def baseEnd_3321987 : Nat := 42117927382409862821851

theorem tailTrace_3321987 : CollatzResearch.WordTrace tailWord_3321987 prefixEnd_3321987 42117927382409862821851 := by
  unfold tailWord_3321987
  simp only [CollatzResearch.WordTrace]
  refine ⟨121162819816015924055652215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80775213210677282703768143 121162819816015924055652215)
  ·
    refine ⟨181744229724023886083478323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121162819816015924055652215 181744229724023886083478323)
    ·
      refine ⟨272616344586035829125217485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181744229724023886083478323 272616344586035829125217485)
      ·
        refine ⟨102231129219763435921956557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272616344586035829125217485 102231129219763435921956557)
        ·
          refine ⟨38336673457411288470733709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102231129219763435921956557 38336673457411288470733709)
          ·
            refine ⟨14376252546529233176525141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38336673457411288470733709 14376252546529233176525141)
            ·
              refine ⟨42117927382409862821851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14376252546529233176525141 42117927382409862821851)
              ·
                rfl

theorem cell22_3321987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 10].length) (baseStart_3321987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321987 prefixEnd_3321987 := by exact prefixLift 3321987
  have htrace : WordTrace (prefixWord ++ tailWord_3321987) baseStart_3321987 baseEnd_3321987 := by
    simpa [prefixWord, tailWord_3321987, baseEnd_3321987] using wordTrace_append hprefix tailTrace_3321987
  have hstable : (prefixWord ++ tailWord_3321987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321987).length < 2 ^ (prefixWord ++ tailWord_3321987).sum := by decide
  have hdescent : baseEnd_3321987 < baseStart_3321987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321989 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_3321989 : Nat := 118140960795 + 3321989 * 2 ^ 59
def prefixEnd_3321989 : Nat := 4983230072969 + 3 ^ 40 * 3321989 * 2
def baseEnd_3321989 : Nat := 1137184723965938957639971

theorem tailTrace_3321989 : CollatzResearch.WordTrace tailWord_3321989 prefixEnd_3321989 1137184723965938957639971 := by
  unfold tailWord_3321989
  simp only [CollatzResearch.WordTrace]
  refine ⟨121162892762008678397225021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80775261841339118931483347 121162892762008678397225021)
  ·
    refine ⟨45436084785753254398959383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121162892762008678397225021 45436084785753254398959383)
    ·
      refine ⟨68154127178629881598439075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45436084785753254398959383 68154127178629881598439075)
      ·
        refine ⟨102231190767944822397658613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68154127178629881598439075 102231190767944822397658613)
        ·
          refine ⟨9584174134494827099780495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102231190767944822397658613 9584174134494827099780495)
          ·
            refine ⟨14376261201742240649670743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584174134494827099780495 14376261201742240649670743)
            ·
              refine ⟨21564391802613360974506115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14376261201742240649670743 21564391802613360974506115)
              ·
                refine ⟨32346587703920041461759173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21564391802613360974506115 32346587703920041461759173)
                ·
                  refine ⟨6064985194485007774079845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32346587703920041461759173 6064985194485007774079845)
                  ·
                    refine ⟨1137184723965938957639971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6064985194485007774079845 1137184723965938957639971)
                    ·
                      rfl

theorem cell22_3321989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_3321989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3321989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3321989 prefixEnd_3321989 := by exact prefixLift 3321989
  have htrace : WordTrace (prefixWord ++ tailWord_3321989) baseStart_3321989 baseEnd_3321989 := by
    simpa [prefixWord, tailWord_3321989, baseEnd_3321989] using wordTrace_append hprefix tailTrace_3321989
  have hstable : (prefixWord ++ tailWord_3321989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321989).length < 2 ^ (prefixWord ++ tailWord_3321989).sum := by decide
  have hdescent : baseEnd_3321989 < baseStart_3321989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322008 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 2, 3]
def baseStart_3322008 : Nat := 118140960795 + 3322008 * 2 ^ 59
def prefixEnd_3322008 : Nat := 4983230072969 + 3 ^ 40 * 3322008 * 2
def baseEnd_3322008 : Nat := 1137191228054229241414913

theorem tailTrace_3322008 : CollatzResearch.WordTrace tailWord_3322008 prefixEnd_3322008 1137191228054229241414913 := by
  unfold tailWord_3322008
  simp only [CollatzResearch.WordTrace]
  refine ⟨60581792874469922321083339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80775723832626563094777785 60581792874469922321083339)
  ·
    refine ⟨90872689311704883481625009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60581792874469922321083339 90872689311704883481625009)
    ·
      refine ⟨68154516983778662611218757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90872689311704883481625009 68154516983778662611218757)
      ·
        refine ⟨12778971934458499239603517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68154516983778662611218757 12778971934458499239603517)
        ·
          refine ⟨4792114475421937214851319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12778971934458499239603517 4792114475421937214851319)
          ·
            refine ⟨7188171713132905822276979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792114475421937214851319 7188171713132905822276979)
            ·
              refine ⟨10782257569699358733415469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7188171713132905822276979 10782257569699358733415469)
              ·
                refine ⟨4043346588637259525030801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10782257569699358733415469 4043346588637259525030801)
                ·
                  refine ⟨3032509941477944643773101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043346588637259525030801 3032509941477944643773101)
                  ·
                    refine ⟨1137191228054229241414913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3032509941477944643773101 1137191228054229241414913)
                    ·
                      rfl

theorem cell22_3322008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_3322008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322008 prefixEnd_3322008 := by exact prefixLift 3322008
  have htrace : WordTrace (prefixWord ++ tailWord_3322008) baseStart_3322008 baseEnd_3322008 := by
    simpa [prefixWord, tailWord_3322008, baseEnd_3322008] using wordTrace_append hprefix tailTrace_3322008
  have hstable : (prefixWord ++ tailWord_3322008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322008).length < 2 ^ (prefixWord ++ tailWord_3322008).sum := by decide
  have hdescent : baseEnd_3322008 < baseStart_3322008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322023 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3322023 : Nat := 118140960795 + 3322023 * 2 ^ 59
def prefixEnd_3322023 : Nat := 4983230072969 + 3 ^ 40 * 3322023 * 2
def baseEnd_3322023 : Nat := 1137196362860774202289867

theorem tailTrace_3322023 : CollatzResearch.WordTrace tailWord_3322023 prefixEnd_3322023 1137196362860774202289867 := by
  unfold tailWord_3322023
  simp only [CollatzResearch.WordTrace]
  refine ⟨121164132843885502203962723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80776088562590334802641815 121164132843885502203962723)
  ·
    refine ⟨181746199265828253305944085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121164132843885502203962723 181746199265828253305944085)
    ·
      refine ⟨8519353090585699373716129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181746199265828253305944085 8519353090585699373716129)
      ·
        refine ⟨6389514817939274530287097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8519353090585699373716129 6389514817939274530287097)
        ·
          refine ⟨4792136113454455897715323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6389514817939274530287097 4792136113454455897715323)
          ·
            refine ⟨7188204170181683846572985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792136113454455897715323 7188204170181683846572985)
            ·
              refine ⟨5391153127636262884929739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7188204170181683846572985 5391153127636262884929739)
              ·
                refine ⟨8086729691454394327394609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391153127636262884929739 8086729691454394327394609)
                ·
                  refine ⟨6065047268590795745545957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086729691454394327394609 6065047268590795745545957)
                  ·
                    refine ⟨1137196362860774202289867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6065047268590795745545957 1137196362860774202289867)
                    ·
                      rfl

theorem cell22_3322023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3322023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322023 prefixEnd_3322023 := by exact prefixLift 3322023
  have htrace : WordTrace (prefixWord ++ tailWord_3322023) baseStart_3322023 baseEnd_3322023 := by
    simpa [prefixWord, tailWord_3322023, baseEnd_3322023] using wordTrace_append hprefix tailTrace_3322023
  have hstable : (prefixWord ++ tailWord_3322023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322023).length < 2 ^ (prefixWord ++ tailWord_3322023).sum := by decide
  have hdescent : baseEnd_3322023 < baseStart_3322023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322066 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_3322066 : Nat := 118140960795 + 3322066 * 2 ^ 59
def prefixEnd_3322066 : Nat := 4983230072969 + 3 ^ 40 * 3322066 * 2
def baseEnd_3322066 : Nat := 379070360879845474488245

theorem tailTrace_3322066 : CollatzResearch.WordTrace tailWord_3322066 prefixEnd_3322066 379070360879845474488245 := by
  unfold tailWord_3322066
  simp only [CollatzResearch.WordTrace]
  refine ⟨30291425295682430136944513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80777134121819813698518701 30291425295682430136944513)
  ·
    refine ⟨22718568971761822602708385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30291425295682430136944513 22718568971761822602708385)
    ·
      refine ⟨17038926728821366952031289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22718568971761822602708385 17038926728821366952031289)
      ·
        refine ⟨12779195046616025214023467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17038926728821366952031289 12779195046616025214023467)
        ·
          refine ⟨19168792569924037821035201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12779195046616025214023467 19168792569924037821035201)
          ·
            refine ⟨14376594427443028365776401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19168792569924037821035201 14376594427443028365776401)
            ·
              refine ⟨10782445820582271274332301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14376594427443028365776401 10782445820582271274332301)
              ·
                refine ⟨4043417182718351727874613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10782445820582271274332301 4043417182718351727874613)
                ·
                  refine ⟨379070360879845474488245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4043417182718351727874613 379070360879845474488245)
                  ·
                    rfl

theorem cell22_3322066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_3322066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322066 prefixEnd_3322066 := by exact prefixLift 3322066
  have htrace : WordTrace (prefixWord ++ tailWord_3322066) baseStart_3322066 baseEnd_3322066 := by
    simpa [prefixWord, tailWord_3322066, baseEnd_3322066] using wordTrace_append hprefix tailTrace_3322066
  have hstable : (prefixWord ++ tailWord_3322066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322066).length < 2 ^ (prefixWord ++ tailWord_3322066).sum := by decide
  have hdescent : baseEnd_3322066 < baseStart_3322066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322070 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3322070 : Nat := 118140960795 + 3322070 * 2 ^ 59
def prefixEnd_3322070 : Nat := 4983230072969 + 3 ^ 40 * 3322070 * 2
def baseEnd_3322070 : Nat := 1137212451921281746364723

theorem tailTrace_3322070 : CollatzResearch.WordTrace tailWord_3322070 prefixEnd_3322070 1137212451921281746364723 := by
  unfold tailWord_3322070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7572865442169701826932729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80777231383143486153949109 7572865442169701826932729)
  ·
    refine ⟨5679649081627276370199547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7572865442169701826932729 5679649081627276370199547)
    ·
      refine ⟨8519473622440914555299321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679649081627276370199547 8519473622440914555299321)
      ·
        refine ⟨6389605216830685916474491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8519473622440914555299321 6389605216830685916474491)
        ·
          refine ⟨9584407825246028874711737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389605216830685916474491 9584407825246028874711737)
          ·
            refine ⟨7188305868934521656033803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9584407825246028874711737 7188305868934521656033803)
            ·
              refine ⟨10782458803401782484050705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7188305868934521656033803 10782458803401782484050705)
              ·
                refine ⟨8086844102551336863038029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10782458803401782484050705 8086844102551336863038029)
                ·
                  refine ⟨3032566538456751323639261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8086844102551336863038029 3032566538456751323639261)
                  ·
                    refine ⟨1137212451921281746364723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3032566538456751323639261 1137212451921281746364723)
                    ·
                      rfl

theorem cell22_3322070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3322070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322070 prefixEnd_3322070 := by exact prefixLift 3322070
  have htrace : WordTrace (prefixWord ++ tailWord_3322070) baseStart_3322070 baseEnd_3322070 := by
    simpa [prefixWord, tailWord_3322070, baseEnd_3322070] using wordTrace_append hprefix tailTrace_3322070
  have hstable : (prefixWord ++ tailWord_3322070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322070).length < 2 ^ (prefixWord ++ tailWord_3322070).sum := by decide
  have hdescent : baseEnd_3322070 < baseStart_3322070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322094 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_3322094 : Nat := 118140960795 + 3322094 * 2 ^ 59
def prefixEnd_3322094 : Nat := 4983230072969 + 3 ^ 40 * 3322094 * 2
def baseEnd_3322094 : Nat := 379073555870584561254883

theorem tailTrace_3322094 : CollatzResearch.WordTrace tailWord_3322094 prefixEnd_3322094 379073555870584561254883 := by
  unfold tailWord_3322094
  simp only [CollatzResearch.WordTrace]
  refine ⟨15145840303328535166224667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80777814951085520886531557 15145840303328535166224667)
  ·
    refine ⟨22718760454992802749337001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15145840303328535166224667 22718760454992802749337001)
    ·
      refine ⟨17039070341244602062002751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22718760454992802749337001 17039070341244602062002751)
      ·
        refine ⟨25558605511866903093004127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17039070341244602062002751 25558605511866903093004127)
        ·
          refine ⟨38337908267800354639506191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25558605511866903093004127 38337908267800354639506191)
          ·
            refine ⟨57506862401700531959259287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38337908267800354639506191 57506862401700531959259287)
            ·
              refine ⟨86260293602550797938888931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57506862401700531959259287 86260293602550797938888931)
              ·
                refine ⟨129390440403826196908333397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86260293602550797938888931 129390440403826196908333397)
                ·
                  refine ⟨379073555870584561254883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129390440403826196908333397 379073555870584561254883)
                  ·
                    rfl

theorem cell22_3322094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_3322094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322094 prefixEnd_3322094 := by exact prefixLift 3322094
  have htrace : WordTrace (prefixWord ++ tailWord_3322094) baseStart_3322094 baseEnd_3322094 := by
    simpa [prefixWord, tailWord_3322094, baseEnd_3322094] using wordTrace_append hprefix tailTrace_3322094
  have hstable : (prefixWord ++ tailWord_3322094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322094).length < 2 ^ (prefixWord ++ tailWord_3322094).sum := by decide
  have hdescent : baseEnd_3322094 < baseStart_3322094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322109 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_3322109 : Nat := 118140960795 + 3322109 * 2 ^ 59
def prefixEnd_3322109 : Nat := 4983230072969 + 3 ^ 40 * 3322109 * 2
def baseEnd_3322109 : Nat := 1137225802418298644639603

theorem tailTrace_3322109 : CollatzResearch.WordTrace tailWord_3322109 prefixEnd_3322109 1137225802418298644639603 := by
  unfold tailWord_3322109
  simp only [CollatzResearch.WordTrace]
  refine ⟨121167269521573938891593381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80778179681049292594395587 121167269521573938891593381)
  ·
    refine ⟨22718863035295113542173759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121167269521573938891593381 22718863035295113542173759)
    ·
      refine ⟨34078294552942670313260639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22718863035295113542173759 34078294552942670313260639)
      ·
        refine ⟨51117441829414005469890959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34078294552942670313260639 51117441829414005469890959)
        ·
          refine ⟨76676162744121008204836439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51117441829414005469890959 76676162744121008204836439)
          ·
            refine ⟨115014244116181512307254659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76676162744121008204836439 115014244116181512307254659)
            ·
              refine ⟨172521366174272268460881989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115014244116181512307254659 172521366174272268460881989)
              ·
                refine ⟨32347756157676050336415373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172521366174272268460881989 32347756157676050336415373)
                ·
                  refine ⟨12130408559128518876155765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32347756157676050336415373 12130408559128518876155765)
                  ·
                    refine ⟨1137225802418298644639603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12130408559128518876155765 1137225802418298644639603)
                    ·
                      rfl

theorem cell22_3322109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_3322109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322109 prefixEnd_3322109 := by exact prefixLift 3322109
  have htrace : WordTrace (prefixWord ++ tailWord_3322109) baseStart_3322109 baseEnd_3322109 := by
    simpa [prefixWord, tailWord_3322109, baseEnd_3322109] using wordTrace_append hprefix tailTrace_3322109
  have hstable : (prefixWord ++ tailWord_3322109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322109).length < 2 ^ (prefixWord ++ tailWord_3322109).sum := by decide
  have hdescent : baseEnd_3322109 < baseStart_3322109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322111 : List Nat := [1, 1, 2, 2, 1, 4, 1, 6, 4]
def baseStart_3322111 : Nat := 118140960795 + 3322111 * 2 ^ 59
def prefixEnd_3322111 : Nat := 4983230072969 + 3 ^ 40 * 3322111 * 2
def baseEnd_3322111 : Nat := 379075495686390435363199

theorem tailTrace_3322111 : CollatzResearch.WordTrace tailWord_3322111 prefixEnd_3322111 379075495686390435363199 := by
  unfold tailWord_3322111
  simp only [CollatzResearch.WordTrace]
  refine ⟨121167342467566693233166187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80778228311711128822110791 121167342467566693233166187)
  ·
    refine ⟨181751013701350039849749281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121167342467566693233166187 181751013701350039849749281)
    ·
      refine ⟨136313260276012529887311961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181751013701350039849749281 136313260276012529887311961)
      ·
        refine ⟨102234945207009397415483971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136313260276012529887311961 102234945207009397415483971)
        ·
          refine ⟨153352417810514096123225957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102234945207009397415483971 153352417810514096123225957)
          ·
            refine ⟨28753578339471393023104867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153352417810514096123225957 28753578339471393023104867)
            ·
              refine ⟨43130367509207089534657301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28753578339471393023104867 43130367509207089534657301)
              ·
                refine ⟨2021735976994082321937061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43130367509207089534657301 2021735976994082321937061)
                ·
                  refine ⟨379075495686390435363199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021735976994082321937061 379075495686390435363199)
                  ·
                    rfl

theorem cell22_3322111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 4].length) (baseStart_3322111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322111 prefixEnd_3322111 := by exact prefixLift 3322111
  have htrace : WordTrace (prefixWord ++ tailWord_3322111) baseStart_3322111 baseEnd_3322111 := by
    simpa [prefixWord, tailWord_3322111, baseEnd_3322111] using wordTrace_append hprefix tailTrace_3322111
  have hstable : (prefixWord ++ tailWord_3322111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322111).length < 2 ^ (prefixWord ++ tailWord_3322111).sum := by decide
  have hdescent : baseEnd_3322111 < baseStart_3322111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322124 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_3322124 : Nat := 118140960795 + 3322124 * 2 ^ 59
def prefixEnd_3322124 : Nat := 4983230072969 + 3 ^ 40 * 3322124 * 2
def baseEnd_3322124 : Nat := 1137230937224843605514557

theorem tailTrace_3322124 : CollatzResearch.WordTrace tailWord_3322124 prefixEnd_3322124 1137230937224843605514557 := by
  unfold tailWord_3322124
  simp only [CollatzResearch.WordTrace]
  refine ⟨60583908308259798226694713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80778544411013064302259617 60583908308259798226694713)
  ·
    refine ⟨45437931231194848670021035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60583908308259798226694713 45437931231194848670021035)
    ·
      refine ⟨68156896846792273005031553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45437931231194848670021035 68156896846792273005031553)
      ·
        refine ⟨51117672635094204753773665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68156896846792273005031553 51117672635094204753773665)
        ·
          refine ⟨38338254476320653565330249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51117672635094204753773665 38338254476320653565330249)
          ·
            refine ⟨28753690857240490173997687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38338254476320653565330249 28753690857240490173997687)
            ·
              refine ⟨43130536285860735260996531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28753690857240490173997687 43130536285860735260996531)
              ·
                refine ⟨64695804428791102891494797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43130536285860735260996531 64695804428791102891494797)
                ·
                  refine ⟨24260926660796663584310549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64695804428791102891494797 24260926660796663584310549)
                  ·
                    refine ⟨1137230937224843605514557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24260926660796663584310549 1137230937224843605514557)
                    ·
                      rfl

theorem cell22_3322124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_3322124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322124 prefixEnd_3322124 := by exact prefixLift 3322124
  have htrace : WordTrace (prefixWord ++ tailWord_3322124) baseStart_3322124 baseEnd_3322124 := by
    simpa [prefixWord, tailWord_3322124, baseEnd_3322124] using wordTrace_append hprefix tailTrace_3322124
  have hstable : (prefixWord ++ tailWord_3322124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322124).length < 2 ^ (prefixWord ++ tailWord_3322124).sum := by decide
  have hdescent : baseEnd_3322124 < baseStart_3322124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322218 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_3322218 : Nat := 118140960795 + 3322218 * 2 ^ 59
def prefixEnd_3322218 : Nat := 4983230072969 + 3 ^ 40 * 3322218 * 2
def baseEnd_3322218 : Nat := 379087705115286231221423

theorem tailTrace_3322218 : CollatzResearch.WordTrace tailWord_3322218 prefixEnd_3322218 379087705115286231221423 := by
  unfold tailWord_3322218
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292811269544762626827827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80780830052119367004874205 30292811269544762626827827)
  ·
    refine ⟨45439216904317143940241741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30292811269544762626827827 45439216904317143940241741)
    ·
      refine ⟨17039706339118928977590653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45439216904317143940241741 17039706339118928977590653)
      ·
        refine ⟨6389889877169598366596495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17039706339118928977590653 6389889877169598366596495)
        ·
          refine ⟨9584834815754397549894743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389889877169598366596495 9584834815754397549894743)
          ·
            refine ⟨14377252223631596324842115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584834815754397549894743 14377252223631596324842115)
            ·
              refine ⟨21565878335447394487263173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14377252223631596324842115 21565878335447394487263173)
              ·
                refine ⟨4043602187896386466361845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21565878335447394487263173 4043602187896386466361845)
                ·
                  refine ⟨379087705115286231221423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4043602187896386466361845 379087705115286231221423)
                  ·
                    rfl

theorem cell22_3322218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_3322218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322218 prefixEnd_3322218 := by exact prefixLift 3322218
  have htrace : WordTrace (prefixWord ++ tailWord_3322218) baseStart_3322218 baseEnd_3322218 := by
    simpa [prefixWord, tailWord_3322218, baseEnd_3322218] using wordTrace_append hprefix tailTrace_3322218
  have hstable : (prefixWord ++ tailWord_3322218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322218).length < 2 ^ (prefixWord ++ tailWord_3322218).sum := by decide
  have hdescent : baseEnd_3322218 < baseStart_3322218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322248 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3322248 : Nat := 118140960795 + 3322248 * 2 ^ 59
def prefixEnd_3322248 : Nat := 4983230072969 + 3 ^ 40 * 3322248 * 2
def baseEnd_3322248 : Nat := 1137273384958948615414177

theorem tailTrace_3322248 : CollatzResearch.WordTrace tailWord_3322248 prefixEnd_3322248 1137273384958948615414177 := by
  unfold tailWord_3322248
  simp only [CollatzResearch.WordTrace]
  refine ⟨60586169634035182815451699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80781559512046910420602265 60586169634035182815451699)
  ·
    refine ⟨90879254451052774223177549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60586169634035182815451699 90879254451052774223177549)
    ·
      refine ⟨34079720419144790333691581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90879254451052774223177549 34079720419144790333691581)
      ·
        refine ⟨12779895157179296375134343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34079720419144790333691581 12779895157179296375134343)
        ·
          refine ⟨19169842735768944562701515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12779895157179296375134343 19169842735768944562701515)
          ·
            refine ⟨28754764103653416844052273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19169842735768944562701515 28754764103653416844052273)
            ·
              refine ⟨21566073077740062633039205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28754764103653416844052273 21566073077740062633039205)
              ·
                refine ⟨4043638702076261743694851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21566073077740062633039205 4043638702076261743694851)
                ·
                  refine ⟨6065458053114392615542277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043638702076261743694851 6065458053114392615542277)
                  ·
                    refine ⟨1137273384958948615414177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6065458053114392615542277 1137273384958948615414177)
                    ·
                      rfl

theorem cell22_3322248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3322248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322248 prefixEnd_3322248 := by exact prefixLift 3322248
  have htrace : WordTrace (prefixWord ++ tailWord_3322248) baseStart_3322248 baseEnd_3322248 := by
    simpa [prefixWord, tailWord_3322248, baseEnd_3322248] using wordTrace_append hprefix tailTrace_3322248
  have hstable : (prefixWord ++ tailWord_3322248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322248).length < 2 ^ (prefixWord ++ tailWord_3322248).sum := by decide
  have hdescent : baseEnd_3322248 < baseStart_3322248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322263 : List Nat := [1, 1, 3, 3, 1, 1, 3, 5, 4]
def baseStart_3322263 : Nat := 118140960795 + 3322263 * 2 ^ 59
def prefixEnd_3322263 : Nat := 4983230072969 + 3 ^ 40 * 3322263 * 2
def baseEnd_3322263 : Nat := 379092839921831192096377

theorem tailTrace_3322263 : CollatzResearch.WordTrace tailWord_3322263 prefixEnd_3322263 379092839921831192096377 := by
  unfold tailWord_3322263
  simp only [CollatzResearch.WordTrace]
  refine ⟨121172886363016023192699443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80781924242010682128466295 121172886363016023192699443)
  ·
    refine ⟨181759329544524034789049165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121172886363016023192699443 181759329544524034789049165)
    ·
      refine ⟨68159748579196513045893437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181759329544524034789049165 68159748579196513045893437)
      ·
        refine ⟨25559905717198692392210039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68159748579196513045893437 25559905717198692392210039)
        ·
          refine ⟨38339858575798038588315059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25559905717198692392210039 38339858575798038588315059)
          ·
            refine ⟨57509787863697057882472589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38339858575798038588315059 57509787863697057882472589)
            ·
              refine ⟨21566170448886396705927221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57509787863697057882472589 21566170448886396705927221)
              ·
                refine ⟨2021828479583099691180677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21566170448886396705927221 2021828479583099691180677)
                ·
                  refine ⟨379092839921831192096377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021828479583099691180677 379092839921831192096377)
                  ·
                    rfl

theorem cell22_3322263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 4].length) (baseStart_3322263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322263 prefixEnd_3322263 := by exact prefixLift 3322263
  have htrace : WordTrace (prefixWord ++ tailWord_3322263) baseStart_3322263 baseEnd_3322263 := by
    simpa [prefixWord, tailWord_3322263, baseEnd_3322263] using wordTrace_append hprefix tailTrace_3322263
  have hstable : (prefixWord ++ tailWord_3322263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322263).length < 2 ^ (prefixWord ++ tailWord_3322263).sum := by decide
  have hdescent : baseEnd_3322263 < baseStart_3322263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322280 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 6]
def baseStart_3322280 : Nat := 118140960795 + 3322280 * 2 ^ 59
def prefixEnd_3322280 : Nat := 4983230072969 + 3 ^ 40 * 3322280 * 2
def baseEnd_3322280 : Nat := 379094779737637066204693

theorem tailTrace_3322280 : CollatzResearch.WordTrace tailWord_3322280 prefixEnd_3322280 379094779737637066204693 := by
  unfold tailWord_3322280
  simp only [CollatzResearch.WordTrace]
  refine ⟨60586753201977217548034147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80782337602636290064045529 60586753201977217548034147)
  ·
    refine ⟨90880129802965826322051221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60586753201977217548034147 90880129802965826322051221)
    ·
      refine ⟨4260006084514023108846151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90880129802965826322051221 4260006084514023108846151)
      ·
        refine ⟨6390009126771034663269227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260006084514023108846151 6390009126771034663269227)
        ·
          refine ⟨9585013690156551994903841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6390009126771034663269227 9585013690156551994903841)
          ·
            refine ⟨7188760267617413996177881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9585013690156551994903841 7188760267617413996177881)
            ·
              refine ⟨5391570200713060497133411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7188760267617413996177881 5391570200713060497133411)
              ·
                refine ⟨8087355301069590745700117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391570200713060497133411 8087355301069590745700117)
                ·
                  refine ⟨379094779737637066204693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8087355301069590745700117 379094779737637066204693)
                  ·
                    rfl

theorem cell22_3322280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_3322280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322280 prefixEnd_3322280 := by exact prefixLift 3322280
  have htrace : WordTrace (prefixWord ++ tailWord_3322280) baseStart_3322280 baseEnd_3322280 := by
    simpa [prefixWord, tailWord_3322280, baseEnd_3322280] using wordTrace_append hprefix tailTrace_3322280
  have hstable : (prefixWord ++ tailWord_3322280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322280).length < 2 ^ (prefixWord ++ tailWord_3322280).sum := by decide
  have hdescent : baseEnd_3322280 < baseStart_3322280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322336 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 7]
def baseStart_3322336 : Nat := 118140960795 + 3322336 * 2 ^ 59
def prefixEnd_3322336 : Nat := 4983230072969 + 3 ^ 40 * 3322336 * 2
def baseEnd_3322336 : Nat := 379101169719115239737969

theorem tailTrace_3322336 : CollatzResearch.WordTrace tailWord_3322336 prefixEnd_3322336 379101169719115239737969 := by
  unfold tailWord_3322336
  simp only [CollatzResearch.WordTrace]
  refine ⟨60587774445875778330053431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80783699261167704440071241 60587774445875778330053431)
  ·
    refine ⟨90881661668813667495080147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60587774445875778330053431 90881661668813667495080147)
    ·
      refine ⟨136322492503220501242620221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90881661668813667495080147 136322492503220501242620221)
      ·
        refine ⟨51120934688707687965982583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136322492503220501242620221 51120934688707687965982583)
        ·
          refine ⟨76681402033061531948973875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51120934688707687965982583 76681402033061531948973875)
          ·
            refine ⟨115022103049592297923460813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76681402033061531948973875 115022103049592297923460813)
            ·
              refine ⟨43133288643597111721297805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115022103049592297923460813 43133288643597111721297805)
              ·
                refine ⟨16174983241348916895486677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43133288643597111721297805 16174983241348916895486677)
                ·
                  refine ⟨379101169719115239737969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16174983241348916895486677 379101169719115239737969)
                  ·
                    rfl

theorem cell22_3322336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_3322336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322336 prefixEnd_3322336 := by exact prefixLift 3322336
  have htrace : WordTrace (prefixWord ++ tailWord_3322336) baseStart_3322336 baseEnd_3322336 := by
    simpa [prefixWord, tailWord_3322336, baseEnd_3322336] using wordTrace_append hprefix tailTrace_3322336
  have hstable : (prefixWord ++ tailWord_3322336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322336).length < 2 ^ (prefixWord ++ tailWord_3322336).sum := by decide
  have hdescent : baseEnd_3322336 < baseStart_3322336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322351 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 1, 7]
def baseStart_3322351 : Nat := 118140960795 + 3322351 * 2 ^ 59
def prefixEnd_3322351 : Nat := 4983230072969 + 3 ^ 40 * 3322351 * 2
def baseEnd_3322351 : Nat := 1137308643963890680088861

theorem tailTrace_3322351 : CollatzResearch.WordTrace tailWord_3322351 prefixEnd_3322351 1137308643963890680088861 := by
  unfold tailWord_3322351
  simp only [CollatzResearch.WordTrace]
  refine ⟨121176095986697214221902907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80784063991131476147935271 121176095986697214221902907)
  ·
    refine ⟨181764143980045821332854361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121176095986697214221902907 181764143980045821332854361)
    ·
      refine ⟨136323107985034365999640771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181764143980045821332854361 136323107985034365999640771)
      ·
        refine ⟨204484661977551548999461157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136323107985034365999640771 204484661977551548999461157)
        ·
          refine ⟨38340874120790915437398967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204484661977551548999461157 38340874120790915437398967)
          ·
            refine ⟨57511311181186373156098451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38340874120790915437398967 57511311181186373156098451)
            ·
              refine ⟨86266966771779559734147677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57511311181186373156098451 86266966771779559734147677)
              ·
                refine ⟨32350112539417334900305379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86266966771779559734147677 32350112539417334900305379)
                ·
                  refine ⟨48525168809126002350458069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32350112539417334900305379 48525168809126002350458069)
                  ·
                    refine ⟨1137308643963890680088861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48525168809126002350458069 1137308643963890680088861)
                    ·
                      rfl

theorem cell22_3322351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_3322351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322351 prefixEnd_3322351 := by exact prefixLift 3322351
  have htrace : WordTrace (prefixWord ++ tailWord_3322351) baseStart_3322351 baseEnd_3322351 := by
    simpa [prefixWord, tailWord_3322351, baseEnd_3322351] using wordTrace_append hprefix tailTrace_3322351
  have hstable : (prefixWord ++ tailWord_3322351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322351).length < 2 ^ (prefixWord ++ tailWord_3322351).sum := by decide
  have hdescent : baseEnd_3322351 < baseStart_3322351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322353 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 5]
def baseStart_3322353 : Nat := 118140960795 + 3322353 * 2 ^ 59
def prefixEnd_3322353 : Nat := 4983230072969 + 3 ^ 40 * 3322353 * 2
def baseEnd_3322353 : Nat := 379103109534921113846285

theorem tailTrace_3322353 : CollatzResearch.WordTrace tailWord_3322353 prefixEnd_3322353 379103109534921113846285 := by
  unfold tailWord_3322353
  simp only [CollatzResearch.WordTrace]
  refine ⟨121176168932689968563475713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80784112621793312375650475 121176168932689968563475713)
  ·
    refine ⟨90882126699517476422606785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121176168932689968563475713 90882126699517476422606785)
    ·
      refine ⟨68161595024638107316955089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90882126699517476422606785 68161595024638107316955089)
      ·
        refine ⟨51121196268478580487716317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68161595024638107316955089 51121196268478580487716317)
        ·
          refine ⟨19170448600679467682893619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51121196268478580487716317 19170448600679467682893619)
          ·
            refine ⟨28755672901019201524340429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19170448600679467682893619 28755672901019201524340429)
            ·
              refine ⟨10783377337882200571627661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28755672901019201524340429 10783377337882200571627661)
              ·
                refine ⟨4043766501705825214360373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10783377337882200571627661 4043766501705825214360373)
                ·
                  refine ⟨379103109534921113846285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4043766501705825214360373 379103109534921113846285)
                  ·
                    rfl

theorem cell22_3322353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_3322353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322353 prefixEnd_3322353 := by exact prefixLift 3322353
  have htrace : WordTrace (prefixWord ++ tailWord_3322353) baseStart_3322353 baseEnd_3322353 := by
    simpa [prefixWord, tailWord_3322353, baseEnd_3322353] using wordTrace_append hprefix tailTrace_3322353
  have hstable : (prefixWord ++ tailWord_3322353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322353).length < 2 ^ (prefixWord ++ tailWord_3322353).sum := by decide
  have hdescent : baseEnd_3322353 < baseStart_3322353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322477 : List Nat := [1, 5, 1, 1, 3, 3, 2, 6]
def baseStart_3322477 : Nat := 118140960795 + 3322477 * 2 ^ 59
def prefixEnd_3322477 : Nat := 4983230072969 + 3 ^ 40 * 3322477 * 2
def baseEnd_3322477 : Nat := 126372419593207594604275

theorem tailTrace_3322477 : CollatzResearch.WordTrace tailWord_3322477 prefixEnd_3322477 126372419593207594604275 := by
  unfold tailWord_3322477
  simp only [CollatzResearch.WordTrace]
  refine ⟨121180691584240737740989685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80787127722827158493993123 121180691584240737740989685)
  ·
    refine ⟨11360689836022569163217783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121180691584240737740989685 11360689836022569163217783)
    ·
      refine ⟨17041034754033853744826675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11360689836022569163217783 17041034754033853744826675)
      ·
        refine ⟨25561552131050780617240013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17041034754033853744826675 25561552131050780617240013)
        ·
          refine ⟨9585582049144042731465005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25561552131050780617240013 9585582049144042731465005)
          ·
            refine ⟨3594593268429016024299377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9585582049144042731465005 3594593268429016024299377)
            ·
              refine ⟨2695944951321762018224533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594593268429016024299377 2695944951321762018224533)
              ·
                refine ⟨126372419593207594604275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2695944951321762018224533 126372419593207594604275)
                ·
                  rfl

theorem cell22_3322477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 6].length) (baseStart_3322477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322477 prefixEnd_3322477 := by exact prefixLift 3322477
  have htrace : WordTrace (prefixWord ++ tailWord_3322477) baseStart_3322477 baseEnd_3322477 := by
    simpa [prefixWord, tailWord_3322477, baseEnd_3322477] using wordTrace_append hprefix tailTrace_3322477
  have hstable : (prefixWord ++ tailWord_3322477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322477).length < 2 ^ (prefixWord ++ tailWord_3322477).sum := by decide
  have hdescent : baseEnd_3322477 < baseStart_3322477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322533 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 8]
def baseStart_3322533 : Nat := 118140960795 + 3322533 * 2 ^ 59
def prefixEnd_3322533 : Nat := 4983230072969 + 3 ^ 40 * 3322533 * 2
def baseEnd_3322533 : Nat := 379123648761100957346101

theorem tailTrace_3322533 : CollatzResearch.WordTrace tailWord_3322533 prefixEnd_3322533 379123648761100957346101 := by
  unfold tailWord_3322533
  simp only [CollatzResearch.WordTrace]
  refine ⟨121182734072037859305028253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80788489381358572870018835 121182734072037859305028253)
  ·
    refine ⟨45443525277014197239385595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121182734072037859305028253 45443525277014197239385595)
    ·
      refine ⟨68165287915521295859078393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45443525277014197239385595 68165287915521295859078393)
      ·
        refine ⟨51123965936640971894308795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68165287915521295859078393 51123965936640971894308795)
        ·
          refine ⟨76685948904961457841463193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51123965936640971894308795 76685948904961457841463193)
          ·
            refine ⟨57514461678721093381097395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76685948904961457841463193 57514461678721093381097395)
            ·
              refine ⟨86271692518081640071646093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57514461678721093381097395 86271692518081640071646093)
              ·
                refine ⟨32351884694280615026867285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86271692518081640071646093 32351884694280615026867285)
                ·
                  refine ⟨379123648761100957346101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32351884694280615026867285 379123648761100957346101)
                  ·
                    rfl

theorem cell22_3322533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_3322533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322533 prefixEnd_3322533 := by exact prefixLift 3322533
  have htrace : WordTrace (prefixWord ++ tailWord_3322533) baseStart_3322533 baseEnd_3322533 := by
    simpa [prefixWord, tailWord_3322533, baseEnd_3322533] using wordTrace_append hprefix tailTrace_3322533
  have hstable : (prefixWord ++ tailWord_3322533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322533).length < 2 ^ (prefixWord ++ tailWord_3322533).sum := by decide
  have hdescent : baseEnd_3322533 < baseStart_3322533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322597 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_3322597 : Nat := 118140960795 + 3322597 * 2 ^ 59
def prefixEnd_3322597 : Nat := 4983230072969 + 3 ^ 40 * 3322597 * 2
def baseEnd_3322597 : Nat := 1137392854791228038438107

theorem tailTrace_3322597 : CollatzResearch.WordTrace tailWord_3322597 prefixEnd_3322597 1137392854791228038438107 := by
  unfold tailWord_3322597
  simp only [CollatzResearch.WordTrace]
  refine ⟨121185068343805998235358045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80790045562537332156905363 121185068343805998235358045)
  ·
    refine ⟨45444400628927249338259267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121185068343805998235358045 45444400628927249338259267)
    ·
      refine ⟨68166600943390874007388901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45444400628927249338259267 68166600943390874007388901)
      ·
        refine ⟨12781237676885788876385419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68166600943390874007388901 12781237676885788876385419)
        ·
          refine ⟨19171856515328683314578129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12781237676885788876385419 19171856515328683314578129)
          ·
            refine ⟨14378892386496512485933597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19171856515328683314578129 14378892386496512485933597)
            ·
              refine ⟨5392084644936192182225099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14378892386496512485933597 5392084644936192182225099)
              ·
                refine ⟨8088126967404288273337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392084644936192182225099 8088126967404288273337649)
                ·
                  refine ⟨6066095225553216205003237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8088126967404288273337649 6066095225553216205003237)
                  ·
                    refine ⟨1137392854791228038438107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6066095225553216205003237 1137392854791228038438107)
                    ·
                      rfl

theorem cell22_3322597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_3322597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322597 prefixEnd_3322597 := by exact prefixLift 3322597
  have htrace : WordTrace (prefixWord ++ tailWord_3322597) baseStart_3322597 baseEnd_3322597 := by
    simpa [prefixWord, tailWord_3322597, baseEnd_3322597] using wordTrace_append hprefix tailTrace_3322597
  have hstable : (prefixWord ++ tailWord_3322597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322597).length < 2 ^ (prefixWord ++ tailWord_3322597).sum := by decide
  have hdescent : baseEnd_3322597 < baseStart_3322597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322678 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3322678 : Nat := 118140960795 + 3322678 * 2 ^ 59
def prefixEnd_3322678 : Nat := 4983230072969 + 3 ^ 40 * 3322678 * 2
def baseEnd_3322678 : Nat := 1137420582746570827162859

theorem tailTrace_3322678 : CollatzResearch.WordTrace tailWord_3322678 prefixEnd_3322678 1137420582746570827162859 := by
  unfold tailWord_3322678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574251416032034316816043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80792015104341699379371125 7574251416032034316816043)
  ·
    refine ⟨11361377124048051475224065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7574251416032034316816043 11361377124048051475224065)
    ·
      refine ⟨8521032843036038606418049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11361377124048051475224065 8521032843036038606418049)
      ·
        refine ⟨6390774632277028954813537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8521032843036038606418049 6390774632277028954813537)
        ·
          refine ⟨4793080974207771716110153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390774632277028954813537 4793080974207771716110153)
          ·
            refine ⟨3594810730655828787082615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4793080974207771716110153 3594810730655828787082615)
            ·
              refine ⟨5392216095983743180623923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594810730655828787082615 5392216095983743180623923)
              ·
                refine ⟨8088324143975614770935885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392216095983743180623923 8088324143975614770935885)
                ·
                  refine ⟨3033121553990855539100957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8088324143975614770935885 3033121553990855539100957)
                  ·
                    refine ⟨1137420582746570827162859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3033121553990855539100957 1137420582746570827162859)
                    ·
                      rfl

theorem cell22_3322678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3322678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322678 prefixEnd_3322678 := by exact prefixLift 3322678
  have htrace : WordTrace (prefixWord ++ tailWord_3322678) baseStart_3322678 baseEnd_3322678 := by
    simpa [prefixWord, tailWord_3322678, baseEnd_3322678] using wordTrace_append hprefix tailTrace_3322678
  have hstable : (prefixWord ++ tailWord_3322678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322678).length < 2 ^ (prefixWord ++ tailWord_3322678).sum := by decide
  have hdescent : baseEnd_3322678 < baseStart_3322678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322730 : List Nat := [3, 1, 3, 15]
def baseStart_3322730 : Nat := 118140960795 + 3322730 * 2 ^ 59
def prefixEnd_3322730 : Nat := 4983230072969 + 3 ^ 40 * 3322730 * 2
def baseEnd_3322730 : Nat := 1560272130876899896931

theorem tailTrace_3322730 : CollatzResearch.WordTrace tailWord_3322730 prefixEnd_3322730 1560272130876899896931 := by
  unfold tailWord_3322730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30297479813081040487487411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80793279501549441299966429 30297479813081040487487411)
  ·
    refine ⟨45446219719621560731231117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30297479813081040487487411 45446219719621560731231117)
    ·
      refine ⟨17042332394858085274211669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45446219719621560731231117 17042332394858085274211669)
      ·
        refine ⟨1560272130876899896931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 17042332394858085274211669 1560272130876899896931)
        ·
          rfl

theorem cell22_3322730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 15].length) (baseStart_3322730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322730 prefixEnd_3322730 := by exact prefixLift 3322730
  have htrace : WordTrace (prefixWord ++ tailWord_3322730) baseStart_3322730 baseEnd_3322730 := by
    simpa [prefixWord, tailWord_3322730, baseEnd_3322730] using wordTrace_append hprefix tailTrace_3322730
  have hstable : (prefixWord ++ tailWord_3322730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322730).length < 2 ^ (prefixWord ++ tailWord_3322730).sum := by decide
  have hdescent : baseEnd_3322730 < baseStart_3322730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322732 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_3322732 : Nat := 118140960795 + 3322732 * 2 ^ 59
def prefixEnd_3322732 : Nat := 4983230072969 + 3 ^ 40 * 3322732 * 2
def baseEnd_3322732 : Nat := 1137439068050132686312693

theorem tailTrace_3322732 : CollatzResearch.WordTrace tailWord_3322732 prefixEnd_3322732 1137439068050132686312693 := by
  unfold tailWord_3322732
  simp only [CollatzResearch.WordTrace]
  refine ⟨60594996099158458145761225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80793328132211277527681633 60594996099158458145761225)
  ·
    refine ⟨45446247074368843609320919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60594996099158458145761225 45446247074368843609320919)
    ·
      refine ⟨68169370611553265413981379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45446247074368843609320919 68169370611553265413981379)
      ·
        refine ⟨102254055917329898120972069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68169370611553265413981379 102254055917329898120972069)
        ·
          refine ⟨19172635484499355897682263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102254055917329898120972069 19172635484499355897682263)
          ·
            refine ⟨28758953226749033846523395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19172635484499355897682263 28758953226749033846523395)
            ·
              refine ⟨43138429840123550769785093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28758953226749033846523395 43138429840123550769785093)
              ·
                refine ⟨8088455595023165769334705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43138429840123550769785093 8088455595023165769334705)
                ·
                  refine ⟨6066341696267374327001029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8088455595023165769334705 6066341696267374327001029)
                  ·
                    refine ⟨1137439068050132686312693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6066341696267374327001029 1137439068050132686312693)
                    ·
                      rfl

theorem cell22_3322732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_3322732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322732 prefixEnd_3322732 := by exact prefixLift 3322732
  have htrace : WordTrace (prefixWord ++ tailWord_3322732) baseStart_3322732 baseEnd_3322732 := by
    simpa [prefixWord, tailWord_3322732, baseEnd_3322732] using wordTrace_append hprefix tailTrace_3322732
  have hstable : (prefixWord ++ tailWord_3322732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322732).length < 2 ^ (prefixWord ++ tailWord_3322732).sum := by decide
  have hdescent : baseEnd_3322732 < baseStart_3322732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322807 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 2, 5]
def baseStart_3322807 : Nat := 118140960795 + 3322807 * 2 ^ 59
def prefixEnd_3322807 : Nat := 4983230072969 + 3 ^ 40 * 3322807 * 2
def baseEnd_3322807 : Nat := 1137464742082857490687463

theorem tailTrace_3322807 : CollatzResearch.WordTrace tailWord_3322807 prefixEnd_3322807 1137464742082857490687463 := by
  unfold tailWord_3322807
  simp only [CollatzResearch.WordTrace]
  refine ⟨121192727673045204100502675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80795151782030136067001783 121192727673045204100502675)
  ·
    refine ⟨181789091509567806150754013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121192727673045204100502675 181789091509567806150754013)
    ·
      refine ⟨68170909316087927306532755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181789091509567806150754013 68170909316087927306532755)
      ·
        refine ⟨102256363974131890959799133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68170909316087927306532755 102256363974131890959799133)
        ·
          refine ⟨38346136490299459109924675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102256363974131890959799133 38346136490299459109924675)
          ·
            refine ⟨57519204735449188664887013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38346136490299459109924675 57519204735449188664887013)
            ·
              refine ⟨10784850887896722874666315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57519204735449188664887013 10784850887896722874666315)
              ·
                refine ⟨16177276331845084311999473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784850887896722874666315 16177276331845084311999473)
                ·
                  refine ⟨12132957248883813233999605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16177276331845084311999473 12132957248883813233999605)
                  ·
                    refine ⟨1137464742082857490687463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12132957248883813233999605 1137464742082857490687463)
                    ·
                      rfl

theorem cell22_3322807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_3322807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322807 prefixEnd_3322807 := by exact prefixLift 3322807
  have htrace : WordTrace (prefixWord ++ tailWord_3322807) baseStart_3322807 baseEnd_3322807 := by
    simpa [prefixWord, tailWord_3322807, baseEnd_3322807] using wordTrace_append hprefix tailTrace_3322807
  have hstable : (prefixWord ++ tailWord_3322807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322807).length < 2 ^ (prefixWord ++ tailWord_3322807).sum := by decide
  have hdescent : baseEnd_3322807 < baseStart_3322807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322852 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3322852 : Nat := 118140960795 + 3322852 * 2 ^ 59
def prefixEnd_3322852 : Nat := 4983230072969 + 3 ^ 40 * 3322852 * 2
def baseEnd_3322852 : Nat := 1137480146502492373312325

theorem tailTrace_3322852 : CollatzResearch.WordTrace tailWord_3322852 prefixEnd_3322852 1137480146502492373312325 := by
  unfold tailWord_3322852
  simp only [CollatzResearch.WordTrace]
  refine ⟨60597184478941088392945405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80796245971921451190593873 60597184478941088392945405)
  ·
    refine ⟨22723944179602908147354527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60597184478941088392945405 22723944179602908147354527)
    ·
      refine ⟨34085916269404362221031791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22723944179602908147354527 34085916269404362221031791)
      ·
        refine ⟨51128874404106543331547687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34085916269404362221031791 51128874404106543331547687)
        ·
          refine ⟨76693311606159814997321531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51128874404106543331547687 76693311606159814997321531)
          ·
            refine ⟨115039967409239722495982297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76693311606159814997321531 115039967409239722495982297)
            ·
              refine ⟨86279975556929791871986723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115039967409239722495982297 86279975556929791871986723)
              ·
                refine ⟨129419963335394687807980085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86279975556929791871986723 129419963335394687807980085)
                ·
                  refine ⟨12133121562693251981998133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129419963335394687807980085 12133121562693251981998133)
                  ·
                    refine ⟨1137480146502492373312325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12133121562693251981998133 1137480146502492373312325)
                    ·
                      rfl

theorem cell22_3322852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3322852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322852 prefixEnd_3322852 := by exact prefixLift 3322852
  have htrace : WordTrace (prefixWord ++ tailWord_3322852) baseStart_3322852 baseEnd_3322852 := by
    simpa [prefixWord, tailWord_3322852, baseEnd_3322852] using wordTrace_append hprefix tailTrace_3322852
  have hstable : (prefixWord ++ tailWord_3322852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322852).length < 2 ^ (prefixWord ++ tailWord_3322852).sum := by decide
  have hdescent : baseEnd_3322852 < baseStart_3322852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322903 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 2, 3]
def baseStart_3322903 : Nat := 118140960795 + 3322903 * 2 ^ 59
def prefixEnd_3322903 : Nat := 4983230072969 + 3 ^ 40 * 3322903 * 2
def baseEnd_3322903 : Nat := 1137497604844745240287169

theorem tailTrace_3322903 : CollatzResearch.WordTrace tailWord_3322903 prefixEnd_3322903 1137497604844745240287169 := by
  unfold tailWord_3322903
  simp only [CollatzResearch.WordTrace]
  refine ⟨121196229080697412495997363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80797486053798274997331575 121196229080697412495997363)
  ·
    refine ⟨181794343621046118743996045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121196229080697412495997363 181794343621046118743996045)
    ·
      refine ⟨68172878857892294528998517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181794343621046118743996045 68172878857892294528998517)
      ·
        refine ⟨6391207392927402612093611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68172878857892294528998517 6391207392927402612093611)
        ·
          refine ⟨9586811089391103918140417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391207392927402612093611 9586811089391103918140417)
          ·
            refine ⟨7190108317043327938605313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9586811089391103918140417 7190108317043327938605313)
            ·
              refine ⟨5392581237782495953953985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7190108317043327938605313 5392581237782495953953985)
              ·
                refine ⟨4044435928336871965465489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392581237782495953953985 4044435928336871965465489)
                ·
                  refine ⟨3033326946252653974099117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4044435928336871965465489 3033326946252653974099117)
                  ·
                    refine ⟨1137497604844745240287169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3033326946252653974099117 1137497604844745240287169)
                    ·
                      rfl

theorem cell22_3322903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_3322903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322903 prefixEnd_3322903 := by exact prefixLift 3322903
  have htrace : WordTrace (prefixWord ++ tailWord_3322903) baseStart_3322903 baseEnd_3322903 := by
    simpa [prefixWord, tailWord_3322903, baseEnd_3322903] using wordTrace_append hprefix tailTrace_3322903
  have hstable : (prefixWord ++ tailWord_3322903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322903).length < 2 ^ (prefixWord ++ tailWord_3322903).sum := by decide
  have hdescent : baseEnd_3322903 < baseStart_3322903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322916 : List Nat := [2, 3, 1, 4, 1, 3, 1, 7]
def baseStart_3322916 : Nat := 118140960795 + 3322916 * 2 ^ 59
def prefixEnd_3322916 : Nat := 4983230072969 + 3 ^ 40 * 3322916 * 2
def baseEnd_3322916 : Nat := 126389117223379726634681

theorem tailTrace_3322916 : CollatzResearch.WordTrace tailWord_3322916 prefixEnd_3322916 126389117223379726634681 := by
  unfold tailWord_3322916
  simp only [CollatzResearch.WordTrace]
  refine ⟨60598351614825157858110301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80797802153100210477480401 60598351614825157858110301)
  ·
    refine ⟨22724381855559434196791363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60598351614825157858110301 22724381855559434196791363)
    ·
      refine ⟨34086572783339151295187045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22724381855559434196791363 34086572783339151295187045)
      ·
        refine ⟨6391232396876090867847571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34086572783339151295187045 6391232396876090867847571)
        ·
          refine ⟨9586848595314136301771357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391232396876090867847571 9586848595314136301771357)
          ·
            refine ⟨3595068223242801113164259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9586848595314136301771357 3595068223242801113164259)
            ·
              refine ⟨5392602334864201669746389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595068223242801113164259 5392602334864201669746389)
              ·
                refine ⟨126389117223379726634681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5392602334864201669746389 126389117223379726634681)
                ·
                  rfl

theorem cell22_3322916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 7].length) (baseStart_3322916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322916 prefixEnd_3322916 := by exact prefixLift 3322916
  have htrace : WordTrace (prefixWord ++ tailWord_3322916) baseStart_3322916 baseEnd_3322916 := by
    simpa [prefixWord, tailWord_3322916, baseEnd_3322916] using wordTrace_append hprefix tailTrace_3322916
  have hstable : (prefixWord ++ tailWord_3322916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322916).length < 2 ^ (prefixWord ++ tailWord_3322916).sum := by decide
  have hdescent : baseEnd_3322916 < baseStart_3322916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322991 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 1, 4]
def baseStart_3322991 : Nat := 118140960795 + 3322991 * 2 ^ 59
def prefixEnd_3322991 : Nat := 4983230072969 + 3 ^ 40 * 3322991 * 2
def baseEnd_3322991 : Nat := 1137527729043142344086899

theorem tailTrace_3322991 : CollatzResearch.WordTrace tailWord_3322991 prefixEnd_3322991 1137527729043142344086899 := by
  unfold tailWord_3322991
  simp only [CollatzResearch.WordTrace]
  refine ⟨121199438704378603525200827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80799625802919069016800551 121199438704378603525200827)
  ·
    refine ⟨181799158056567905287801241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121199438704378603525200827 181799158056567905287801241)
    ·
      refine ⟨136349368542425928965850931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181799158056567905287801241 136349368542425928965850931)
      ·
        refine ⟨204524052813638893448776397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136349368542425928965850931 204524052813638893448776397)
        ·
          refine ⟨76696519805114585043291149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204524052813638893448776397 76696519805114585043291149)
          ·
            refine ⟨28761194926917969391234181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76696519805114585043291149 28761194926917969391234181)
            ·
              refine ⟨5392724048797119260856409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28761194926917969391234181 5392724048797119260856409)
              ·
                refine ⟨4044543036597839445642307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392724048797119260856409 4044543036597839445642307)
                ·
                  refine ⟨6066814554896759168463461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044543036597839445642307 6066814554896759168463461)
                  ·
                    refine ⟨1137527729043142344086899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6066814554896759168463461 1137527729043142344086899)
                    ·
                      rfl

theorem cell22_3322991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_3322991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3322991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3322991 prefixEnd_3322991 := by exact prefixLift 3322991
  have htrace : WordTrace (prefixWord ++ tailWord_3322991) baseStart_3322991 baseEnd_3322991 := by
    simpa [prefixWord, tailWord_3322991, baseEnd_3322991] using wordTrace_append hprefix tailTrace_3322991
  have hstable : (prefixWord ++ tailWord_3322991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322991).length < 2 ^ (prefixWord ++ tailWord_3322991).sum := by decide
  have hdescent : baseEnd_3322991 < baseStart_3322991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323004 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_3323004 : Nat := 118140960795 + 3323004 * 2 ^ 59
def prefixEnd_3323004 : Nat := 4983230072969 + 3 ^ 40 * 3323004 * 2
def baseEnd_3323004 : Nat := 1137532179208814643511859

theorem tailTrace_3323004 : CollatzResearch.WordTrace tailWord_3323004 prefixEnd_3323004 1137532179208814643511859 := by
  unfold tailWord_3323004
  simp only [CollatzResearch.WordTrace]
  refine ⟨60599956426665753372712033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80799941902221004496949377 60599956426665753372712033)
  ·
    refine ⟨45449967319999315029534025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60599956426665753372712033 45449967319999315029534025)
    ·
      refine ⟨34087475489999486272150519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45449967319999315029534025 34087475489999486272150519)
      ·
        refine ⟨51131213234999229408225779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34087475489999486272150519 51131213234999229408225779)
        ·
          refine ⟨76696819852498844112338669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51131213234999229408225779 76696819852498844112338669)
          ·
            refine ⟨28761307444687066542127001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76696819852498844112338669 28761307444687066542127001)
            ·
              refine ⟨21570980583515299906595251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28761307444687066542127001 21570980583515299906595251)
              ·
                refine ⟨32356470875272949859892877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21570980583515299906595251 32356470875272949859892877)
                ·
                  refine ⟨12133676578227356197459829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32356470875272949859892877 12133676578227356197459829)
                  ·
                    refine ⟨1137532179208814643511859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12133676578227356197459829 1137532179208814643511859)
                    ·
                      rfl

theorem cell22_3323004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_3323004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323004 prefixEnd_3323004 := by exact prefixLift 3323004
  have htrace : WordTrace (prefixWord ++ tailWord_3323004) baseStart_3323004 baseEnd_3323004 := by
    simpa [prefixWord, tailWord_3323004, baseEnd_3323004] using wordTrace_append hprefix tailTrace_3323004
  have hstable : (prefixWord ++ tailWord_3323004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323004).length < 2 ^ (prefixWord ++ tailWord_3323004).sum := by decide
  have hdescent : baseEnd_3323004 < baseStart_3323004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323042 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3323042 : Nat := 118140960795 + 3323042 * 2 ^ 59
def prefixEnd_3323042 : Nat := 4983230072969 + 3 ^ 40 * 3323042 * 2
def baseEnd_3323042 : Nat := 1137545187385395211061743

theorem tailTrace_3323042 : CollatzResearch.WordTrace tailWord_3323042 prefixEnd_3323042 1137545187385395211061743 := by
  unfold tailWord_3323042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30300324706798459808826845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80800865884795892823538253 30300324706798459808826845)
  ·
    refine ⟨11362621765049422428310067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30300324706798459808826845 11362621765049422428310067)
    ·
      refine ⟨17043932647574133642465101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11362621765049422428310067 17043932647574133642465101)
      ·
        refine ⟨6391474742840300115924413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17043932647574133642465101 6391474742840300115924413)
        ·
          refine ⟨2396803028565112543471655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6391474742840300115924413 2396803028565112543471655)
          ·
            refine ⟨3595204542847668815207483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396803028565112543471655 3595204542847668815207483)
            ·
              refine ⟨5392806814271503222811225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595204542847668815207483 5392806814271503222811225)
              ·
                refine ⟨4044605110703627417108419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392806814271503222811225 4044605110703627417108419)
                ·
                  refine ⟨6066907666055441125662629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044605110703627417108419 6066907666055441125662629)
                  ·
                    refine ⟨1137545187385395211061743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6066907666055441125662629 1137545187385395211061743)
                    ·
                      rfl

theorem cell22_3323042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3323042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323042 prefixEnd_3323042 := by exact prefixLift 3323042
  have htrace : WordTrace (prefixWord ++ tailWord_3323042) baseStart_3323042 baseEnd_3323042 := by
    simpa [prefixWord, tailWord_3323042, baseEnd_3323042] using wordTrace_append hprefix tailTrace_3323042
  have hstable : (prefixWord ++ tailWord_3323042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323042).length < 2 ^ (prefixWord ++ tailWord_3323042).sum := by decide
  have hdescent : baseEnd_3323042 < baseStart_3323042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323079 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 7]
def baseStart_3323079 : Nat := 118140960795 + 3323079 * 2 ^ 59
def prefixEnd_3323079 : Nat := 4983230072969 + 3 ^ 40 * 3323079 * 2
def baseEnd_3323079 : Nat := 379185951080513149295543

theorem tailTrace_3323079 : CollatzResearch.WordTrace tailWord_3323079 prefixEnd_3323079 379185951080513149295543 := by
  unfold tailWord_3323079
  simp only [CollatzResearch.WordTrace]
  refine ⟨121202648328059794554404291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80801765552039863036269527 121202648328059794554404291)
  ·
    refine ⟨181803972492089691831606437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121202648328059794554404291 181803972492089691831606437)
    ·
      refine ⟨34088244842266817218426207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181803972492089691831606437 34088244842266817218426207)
      ·
        refine ⟨51132367263400225827639311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34088244842266817218426207 51132367263400225827639311)
        ·
          refine ⟨76698550895100338741458967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51132367263400225827639311 76698550895100338741458967)
          ·
            refine ⟨115047826342650508112188451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76698550895100338741458967 115047826342650508112188451)
            ·
              refine ⟨172571739513975762168282677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115047826342650508112188451 172571739513975762168282677)
              ·
                refine ⟨16178600579435227703276501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172571739513975762168282677 16178600579435227703276501)
                ·
                  refine ⟨379185951080513149295543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16178600579435227703276501 379185951080513149295543)
                  ·
                    rfl

theorem cell22_3323079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 7].length) (baseStart_3323079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323079 prefixEnd_3323079 := by exact prefixLift 3323079
  have htrace : WordTrace (prefixWord ++ tailWord_3323079) baseStart_3323079 baseEnd_3323079 := by
    simpa [prefixWord, tailWord_3323079, baseEnd_3323079] using wordTrace_append hprefix tailTrace_3323079
  have hstable : (prefixWord ++ tailWord_3323079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323079).length < 2 ^ (prefixWord ++ tailWord_3323079).sum := by decide
  have hdescent : baseEnd_3323079 < baseStart_3323079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323117 : List Nat := [1, 5, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_3323117 : Nat := 118140960795 + 3323117 * 2 ^ 59
def prefixEnd_3323117 : Nat := 4983230072969 + 3 ^ 40 * 3323117 * 2
def baseEnd_3323117 : Nat := 1137570861418120015436513

theorem tailTrace_3323117 : CollatzResearch.WordTrace tailWord_3323117 prefixEnd_3323117 1137570861418120015436513 := by
  unfold tailWord_3323117
  simp only [CollatzResearch.WordTrace]
  refine ⟨121204034301922127044287605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80802689534614751362858403 121204034301922127044287605)
  ·
    refine ⟨11362878215805199410401963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121204034301922127044287605 11362878215805199410401963)
    ·
      refine ⟨17044317323707799115602945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11362878215805199410401963 17044317323707799115602945)
      ·
        refine ⟨12783237992780849336702209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17044317323707799115602945 12783237992780849336702209)
        ·
          refine ⟨9587428494585637002526657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12783237992780849336702209 9587428494585637002526657)
          ·
            refine ⟨7190571370939227751894993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9587428494585637002526657 7190571370939227751894993)
            ·
              refine ⟨5392928528204420813921245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7190571370939227751894993 5392928528204420813921245)
              ·
                refine ⟨2022348198076657805220467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5392928528204420813921245 2022348198076657805220467)
                ·
                  refine ⟨3033522297114986707830701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022348198076657805220467 3033522297114986707830701)
                  ·
                    refine ⟨1137570861418120015436513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3033522297114986707830701 1137570861418120015436513)
                    ·
                      rfl

theorem cell22_3323117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_3323117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323117 prefixEnd_3323117 := by exact prefixLift 3323117
  have htrace : WordTrace (prefixWord ++ tailWord_3323117) baseStart_3323117 baseEnd_3323117 := by
    simpa [prefixWord, tailWord_3323117, baseEnd_3323117] using wordTrace_append hprefix tailTrace_3323117
  have hstable : (prefixWord ++ tailWord_3323117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323117).length < 2 ^ (prefixWord ++ tailWord_3323117).sum := by decide
  have hdescent : baseEnd_3323117 < baseStart_3323117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323141 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 6]
def baseStart_3323141 : Nat := 118140960795 + 3323141 * 2 ^ 59
def prefixEnd_3323141 : Nat := 4983230072969 + 3 ^ 40 * 3323141 * 2
def baseEnd_3323141 : Nat := 379193025702863984278813

theorem tailTrace_3323141 : CollatzResearch.WordTrace tailWord_3323141 prefixEnd_3323141 379193025702863984278813 := by
  unfold tailWord_3323141
  simp only [CollatzResearch.WordTrace]
  refine ⟨121204909653835179143161277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80803273102556786095440851 121204909653835179143161277)
  ·
    refine ⟨45451841120188192178685479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121204909653835179143161277 45451841120188192178685479)
    ·
      refine ⟨68177761680282288268028219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45451841120188192178685479 68177761680282288268028219)
      ·
        refine ⟨102266642520423432402042329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68177761680282288268028219 102266642520423432402042329)
        ·
          refine ⟨76699981890317574301531747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102266642520423432402042329 76699981890317574301531747)
          ·
            refine ⟨115049972835476361452297621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76699981890317574301531747 115049972835476361452297621)
            ·
              refine ⟨5392967476662954443076451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115049972835476361452297621 5392967476662954443076451)
              ·
                refine ⟨8089451214994431664614677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392967476662954443076451 8089451214994431664614677)
                ·
                  refine ⟨379193025702863984278813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8089451214994431664614677 379193025702863984278813)
                  ·
                    rfl

theorem cell22_3323141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_3323141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323141 prefixEnd_3323141 := by exact prefixLift 3323141
  have htrace : WordTrace (prefixWord ++ tailWord_3323141) baseStart_3323141 baseEnd_3323141 := by
    simpa [prefixWord, tailWord_3323141, baseEnd_3323141] using wordTrace_append hprefix tailTrace_3323141
  have hstable : (prefixWord ++ tailWord_3323141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323141).length < 2 ^ (prefixWord ++ tailWord_3323141).sum := by decide
  have hdescent : baseEnd_3323141 < baseStart_3323141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323171 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 1, 6]
def baseStart_3323171 : Nat := 118140960795 + 3323171 * 2 ^ 59
def prefixEnd_3323171 : Nat := 4983230072969 + 3 ^ 40 * 3323171 * 2
def baseEnd_3323171 : Nat := 1137589346721681874586347

theorem tailTrace_3323171 : CollatzResearch.WordTrace tailWord_3323171 prefixEnd_3323171 1137589346721681874586347 := by
  unfold tailWord_3323171
  simp only [CollatzResearch.WordTrace]
  refine ⟨121206003843726494266753367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80804002562484329511168911 121206003843726494266753367)
  ·
    refine ⟨181809005765589741400130051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121206003843726494266753367 181809005765589741400130051)
    ·
      refine ⟨272713508648384612100195077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181809005765589741400130051 272713508648384612100195077)
      ·
        refine ⟨51133782871572114768786577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272713508648384612100195077 51133782871572114768786577)
        ·
          refine ⟨38350337153679086076589933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51133782871572114768786577 38350337153679086076589933)
          ·
            refine ⟨14381376432629657278721225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38350337153679086076589933 14381376432629657278721225)
            ·
              refine ⟨10786032324472242959040919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14381376432629657278721225 10786032324472242959040919)
              ·
                refine ⟨16179048486708364438561379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10786032324472242959040919 16179048486708364438561379)
                ·
                  refine ⟨24268572730062546657842069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16179048486708364438561379 24268572730062546657842069)
                  ·
                    refine ⟨1137589346721681874586347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24268572730062546657842069 1137589346721681874586347)
                    ·
                      rfl

theorem cell22_3323171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_3323171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323171 prefixEnd_3323171 := by exact prefixLift 3323171
  have htrace : WordTrace (prefixWord ++ tailWord_3323171) baseStart_3323171 baseEnd_3323171 := by
    simpa [prefixWord, tailWord_3323171, baseEnd_3323171] using wordTrace_append hprefix tailTrace_3323171
  have hstable : (prefixWord ++ tailWord_3323171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323171).length < 2 ^ (prefixWord ++ tailWord_3323171).sum := by decide
  have hdescent : baseEnd_3323171 < baseStart_3323171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323173 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_3323173 : Nat := 118140960795 + 3323173 * 2 ^ 59
def prefixEnd_3323173 : Nat := 4983230072969 + 3 ^ 40 * 3323173 * 2
def baseEnd_3323173 : Nat := 1137590031362554536036341

theorem tailTrace_3323173 : CollatzResearch.WordTrace tailWord_3323173 prefixEnd_3323173 1137590031362554536036341 := by
  unfold tailWord_3323173
  simp only [CollatzResearch.WordTrace]
  refine ⟨121206076789719248608326173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80804051193146165738884115 121206076789719248608326173)
  ·
    refine ⟨45452278796144718228122315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121206076789719248608326173 45452278796144718228122315)
    ·
      refine ⟨68178418194217077342183473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45452278796144718228122315 68178418194217077342183473)
      ·
        refine ⟨51133813645662808006637605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68178418194217077342183473 51133813645662808006637605)
        ·
          refine ⟨9587590058561776501244551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51133813645662808006637605 9587590058561776501244551)
          ·
            refine ⟨14381385087842664751866827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9587590058561776501244551 14381385087842664751866827)
            ·
              refine ⟨21572077631763997127800241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14381385087842664751866827 21572077631763997127800241)
              ·
                refine ⟨16179058223822997845850181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21572077631763997127800241 16179058223822997845850181)
                ·
                  refine ⟨3033573416966812096096909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16179058223822997845850181 3033573416966812096096909)
                  ·
                    refine ⟨1137590031362554536036341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3033573416966812096096909 1137590031362554536036341)
                    ·
                      rfl

theorem cell22_3323173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_3323173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323173 prefixEnd_3323173 := by exact prefixLift 3323173
  have htrace : WordTrace (prefixWord ++ tailWord_3323173) baseStart_3323173 baseEnd_3323173 := by
    simpa [prefixWord, tailWord_3323173, baseEnd_3323173] using wordTrace_append hprefix tailTrace_3323173
  have hstable : (prefixWord ++ tailWord_3323173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323173).length < 2 ^ (prefixWord ++ tailWord_3323173).sum := by decide
  have hdescent : baseEnd_3323173 < baseStart_3323173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323186 : List Nat := [3, 2, 1, 1, 4, 1, 10]
def baseStart_3323186 : Nat := 118140960795 + 3323186 * 2 ^ 59
def prefixEnd_3323186 : Nat := 4983230072969 + 3 ^ 40 * 3323186 * 2
def baseEnd_3323186 : Nat := 42133128945489882794863

theorem tailTrace_3323186 : CollatzResearch.WordTrace tailWord_3323186 prefixEnd_3323186 42133128945489882794863 := by
  unfold tailWord_3323186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30301637734668037957137353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80804367292448101219032941 30301637734668037957137353)
  ·
    refine ⟨22726228301001028467853015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30301637734668037957137353 22726228301001028467853015)
    ·
      refine ⟨34089342451501542701779523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22726228301001028467853015 34089342451501542701779523)
      ·
        refine ⟨51134013677252314052669285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34089342451501542701779523 51134013677252314052669285)
        ·
          refine ⟨9587627564484808884875491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51134013677252314052669285 9587627564484808884875491)
          ·
            refine ⟨14381441346727213327313237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9587627564484808884875491 14381441346727213327313237)
            ·
              refine ⟨42133128945489882794863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14381441346727213327313237 42133128945489882794863)
              ·
                rfl

theorem cell22_3323186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 10].length) (baseStart_3323186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323186 prefixEnd_3323186 := by exact prefixLift 3323186
  have htrace : WordTrace (prefixWord ++ tailWord_3323186) baseStart_3323186 baseEnd_3323186 := by
    simpa [prefixWord, tailWord_3323186, baseEnd_3323186] using wordTrace_append hprefix tailTrace_3323186
  have hstable : (prefixWord ++ tailWord_3323186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323186).length < 2 ^ (prefixWord ++ tailWord_3323186).sum := by decide
  have hdescent : baseEnd_3323186 < baseStart_3323186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323207 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 2, 3]
def baseStart_3323207 : Nat := 118140960795 + 3323207 * 2 ^ 59
def prefixEnd_3323207 : Nat := 4983230072969 + 3 ^ 40 * 3323207 * 2
def baseEnd_3323207 : Nat := 1137601670257389780686237

theorem tailTrace_3323207 : CollatzResearch.WordTrace tailWord_3323207 prefixEnd_3323207 1137601670257389780686237 := by
  unfold tailWord_3323207
  simp only [CollatzResearch.WordTrace]
  refine ⟨121207316871596072415063875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80804877914397381610042583 121207316871596072415063875)
  ·
    refine ⟨181810975307394108622595813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121207316871596072415063875 181810975307394108622595813)
    ·
      refine ⟨34089557870136395366736715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181810975307394108622595813 34089557870136395366736715)
      ·
        refine ⟨51134336805204593050105073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34089557870136395366736715 51134336805204593050105073)
        ·
          refine ⟨38350752603903444787578805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51134336805204593050105073 38350752603903444787578805)
          ·
            refine ⟨3595383056615947948835513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38350752603903444787578805 3595383056615947948835513)
            ·
              refine ⟨2696537292461960961626635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3595383056615947948835513 2696537292461960961626635)
              ·
                refine ⟨4044805938692941442439953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696537292461960961626635 4044805938692941442439953)
                ·
                  refine ⟨3033604454019706081829965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4044805938692941442439953 3033604454019706081829965)
                  ·
                    refine ⟨1137601670257389780686237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3033604454019706081829965 1137601670257389780686237)
                    ·
                      rfl

theorem cell22_3323207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_3323207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323207 prefixEnd_3323207 := by exact prefixLift 3323207
  have htrace : WordTrace (prefixWord ++ tailWord_3323207) baseStart_3323207 baseEnd_3323207 := by
    simpa [prefixWord, tailWord_3323207, baseEnd_3323207] using wordTrace_append hprefix tailTrace_3323207
  have hstable : (prefixWord ++ tailWord_3323207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323207).length < 2 ^ (prefixWord ++ tailWord_3323207).sum := by decide
  have hdescent : baseEnd_3323207 < baseStart_3323207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323218 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_3323218 : Nat := 118140960795 + 3323218 * 2 ^ 59
def prefixEnd_3323218 : Nat := 4983230072969 + 3 ^ 40 * 3323218 * 2
def baseEnd_3323218 : Nat := 1137605435782189418661203

theorem tailTrace_3323218 : CollatzResearch.WordTrace tailWord_3323218 prefixEnd_3323218 1137605435782189418661203 := by
  unfold tailWord_3323218
  simp only [CollatzResearch.WordTrace]
  refine ⟨30301929518639055323428577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80805145383037480862476205 30301929518639055323428577)
  ·
    refine ⟨22726447138979291492571433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30301929518639055323428577 22726447138979291492571433)
    ·
      refine ⟨17044835354234468619428575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22726447138979291492571433 17044835354234468619428575)
      ·
        refine ⟨25567253031351702929142863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17044835354234468619428575 25567253031351702929142863)
        ·
          refine ⟨38350879547027554393714295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25567253031351702929142863 38350879547027554393714295)
          ·
            refine ⟨57526319320541331590571443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38350879547027554393714295 57526319320541331590571443)
            ·
              refine ⟨86289478980811997385857165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57526319320541331590571443 86289478980811997385857165)
              ·
                refine ⟨32358554617804499019696437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86289478980811997385857165 32358554617804499019696437)
                ·
                  refine ⟨3033614495419171783096541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32358554617804499019696437 3033614495419171783096541)
                  ·
                    refine ⟨1137605435782189418661203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3033614495419171783096541 1137605435782189418661203)
                    ·
                      rfl

theorem cell22_3323218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_3323218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323218 prefixEnd_3323218 := by exact prefixLift 3323218
  have htrace : WordTrace (prefixWord ++ tailWord_3323218) baseStart_3323218 baseEnd_3323218 := by
    simpa [prefixWord, tailWord_3323218, baseEnd_3323218] using wordTrace_append hprefix tailTrace_3323218
  have hstable : (prefixWord ++ tailWord_3323218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323218).length < 2 ^ (prefixWord ++ tailWord_3323218).sum := by decide
  have hdescent : baseEnd_3323218 < baseStart_3323218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323248 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 5]
def baseStart_3323248 : Nat := 118140960795 + 3323248 * 2 ^ 59
def prefixEnd_3323248 : Nat := 4983230072969 + 3 ^ 40 * 3323248 * 2
def baseEnd_3323248 : Nat := 379205235131759780137037

theorem tailTrace_3323248 : CollatzResearch.WordTrace tailWord_3323248 prefixEnd_3323248 379205235131759780137037 := by
  unfold tailWord_3323248
  simp only [CollatzResearch.WordTrace]
  refine ⟨60604406132223768208653199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80805874842965024278204265 60604406132223768208653199)
  ·
    refine ⟨90906609198335652312979799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60604406132223768208653199 90906609198335652312979799)
    ·
      refine ⟨136359913797503478469469699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90906609198335652312979799 136359913797503478469469699)
      ·
        refine ⟨204539870696255217704204549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136359913797503478469469699 204539870696255217704204549)
        ·
          refine ⟨38351225755547853319538353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204539870696255217704204549 38351225755547853319538353)
          ·
            refine ⟨28763419316660889989653765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38351225755547853319538353 28763419316660889989653765)
            ·
              refine ⟨5393141121873916873060081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28763419316660889989653765 5393141121873916873060081)
              ·
                refine ⟨4044855841405437654795061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5393141121873916873060081 4044855841405437654795061)
                ·
                  refine ⟨379205235131759780137037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4044855841405437654795061 379205235131759780137037)
                  ·
                    rfl

theorem cell22_3323248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_3323248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323248 prefixEnd_3323248 := by exact prefixLift 3323248
  have htrace : WordTrace (prefixWord ++ tailWord_3323248) baseStart_3323248 baseEnd_3323248 := by
    simpa [prefixWord, tailWord_3323248, baseEnd_3323248] using wordTrace_append hprefix tailTrace_3323248
  have hstable : (prefixWord ++ tailWord_3323248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323248).length < 2 ^ (prefixWord ++ tailWord_3323248).sum := by decide
  have hdescent : baseEnd_3323248 < baseStart_3323248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323295 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 1, 4]
def baseStart_3323295 : Nat := 118140960795 + 3323295 * 2 ^ 59
def prefixEnd_3323295 : Nat := 4983230072969 + 3 ^ 40 * 3323295 * 2
def baseEnd_3323295 : Nat := 1137631794455786884485967

theorem tailTrace_3323295 : CollatzResearch.WordTrace tailWord_3323295 prefixEnd_3323295 1137631794455786884485967 := by
  unfold tailWord_3323295
  simp only [CollatzResearch.WordTrace]
  refine ⟨121210526495277263444267339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80807017663518175629511559 121210526495277263444267339)
  ·
    refine ⟨181815789742915895166401009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121210526495277263444267339 181815789742915895166401009)
    ·
      refine ⟨136361842307186921374800757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181815789742915895166401009 136361842307186921374800757)
      ·
        refine ⟨12783922716298773878887571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136361842307186921374800757 12783922716298773878887571)
        ·
          refine ⟨19175884074448160818331357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12783922716298773878887571 19175884074448160818331357)
          ·
            refine ⟨7190956527918060306874259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19175884074448160818331357 7190956527918060306874259)
            ·
              refine ⟨10786434791877090460311389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190956527918060306874259 10786434791877090460311389)
              ·
                refine ⟨4044913046953908922616771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10786434791877090460311389 4044913046953908922616771)
                ·
                  refine ⟨6067369570430863383925157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044913046953908922616771 6067369570430863383925157)
                  ·
                    refine ⟨1137631794455786884485967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6067369570430863383925157 1137631794455786884485967)
                    ·
                      rfl

theorem cell22_3323295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_3323295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323295 prefixEnd_3323295 := by exact prefixLift 3323295
  have htrace : WordTrace (prefixWord ++ tailWord_3323295) baseStart_3323295 baseEnd_3323295 := by
    simpa [prefixWord, tailWord_3323295, baseEnd_3323295] using wordTrace_append hprefix tailTrace_3323295
  have hstable : (prefixWord ++ tailWord_3323295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323295).length < 2 ^ (prefixWord ++ tailWord_3323295).sum := by decide
  have hdescent : baseEnd_3323295 < baseStart_3323295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323338 : List Nat := [3, 1, 2, 1, 2, 4, 1, 8]
def baseStart_3323338 : Nat := 118140960795 + 3323338 * 2 ^ 59
def prefixEnd_3323338 : Nat := 4983230072969 + 3 ^ 40 * 3323338 * 2
def baseEnd_3323338 : Nat := 126405168248283233962315

theorem tailTrace_3323338 : CollatzResearch.WordTrace tailWord_3323338 prefixEnd_3323338 126405168248283233962315 := by
  unfold tailWord_3323338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30303023708530370447020667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80808063222747654525388445 30303023708530370447020667)
  ·
    refine ⟨45454535562795555670531001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30303023708530370447020667 45454535562795555670531001)
    ·
      refine ⟨34090901672096666752898251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45454535562795555670531001 34090901672096666752898251)
      ·
        refine ⟨51136352508145000129347377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34090901672096666752898251 51136352508145000129347377)
        ·
          refine ⟨38352264381108750097010533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51136352508145000129347377 38352264381108750097010533)
          ·
            refine ⟨7191049571457890643189475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38352264381108750097010533 7191049571457890643189475)
            ·
              refine ⟨10786574357186835964784213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191049571457890643189475 10786574357186835964784213)
              ·
                refine ⟨126405168248283233962315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10786574357186835964784213 126405168248283233962315)
                ·
                  rfl

theorem cell22_3323338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_3323338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323338 prefixEnd_3323338 := by exact prefixLift 3323338
  have htrace : WordTrace (prefixWord ++ tailWord_3323338) baseStart_3323338 baseEnd_3323338 := by
    simpa [prefixWord, tailWord_3323338, baseEnd_3323338] using wordTrace_append hprefix tailTrace_3323338
  have hstable : (prefixWord ++ tailWord_3323338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323338).length < 2 ^ (prefixWord ++ tailWord_3323338).sum := by decide
  have hdescent : baseEnd_3323338 < baseStart_3323338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323368 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3323368 : Nat := 118140960795 + 3323368 * 2 ^ 59
def prefixEnd_3323368 : Nat := 4983230072969 + 3 ^ 40 * 3323368 * 2
def baseEnd_3323368 : Nat := 1137656783847639027410743

theorem tailTrace_3323368 : CollatzResearch.WordTrace tailWord_3323368 prefixEnd_3323368 1137656783847639027410743 := by
  unfold tailWord_3323368
  simp only [CollatzResearch.WordTrace]
  refine ⟨60606594512006398455837379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80808792682675197941116505 60606594512006398455837379)
  ·
    refine ⟨90909891768009597683756069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60606594512006398455837379 90909891768009597683756069)
    ·
      refine ⟨17045604706501799565704263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90909891768009597683756069 17045604706501799565704263)
      ·
        refine ⟨25568407059752699348556395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17045604706501799565704263 25568407059752699348556395)
        ·
          refine ⟨38352610589629049022834593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25568407059752699348556395 38352610589629049022834593)
          ·
            refine ⟨28764457942221786767125945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38352610589629049022834593 28764457942221786767125945)
            ·
              refine ⟨21573343456666340075344459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28764457942221786767125945 21573343456666340075344459)
              ·
                refine ⟨32360015184999510113016689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21573343456666340075344459 32360015184999510113016689)
                ·
                  refine ⟨24270011388749632584762517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32360015184999510113016689 24270011388749632584762517)
                  ·
                    refine ⟨1137656783847639027410743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24270011388749632584762517 1137656783847639027410743)
                    ·
                      rfl

theorem cell22_3323368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3323368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323368 prefixEnd_3323368 := by exact prefixLift 3323368
  have htrace : WordTrace (prefixWord ++ tailWord_3323368) baseStart_3323368 baseEnd_3323368 := by
    simpa [prefixWord, tailWord_3323368, baseEnd_3323368] using wordTrace_append hprefix tailTrace_3323368
  have hstable : (prefixWord ++ tailWord_3323368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323368).length < 2 ^ (prefixWord ++ tailWord_3323368).sum := by decide
  have hdescent : baseEnd_3323368 < baseStart_3323368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323432 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3323432 : Nat := 118140960795 + 3323432 * 2 ^ 59
def prefixEnd_3323432 : Nat := 4983230072969 + 3 ^ 40 * 3323432 * 2
def baseEnd_3323432 : Nat := 1137678692355564193810547

theorem tailTrace_3323432 : CollatzResearch.WordTrace tailWord_3323432 prefixEnd_3323432 1137678692355564193810547 := by
  unfold tailWord_3323432
  simp only [CollatzResearch.WordTrace]
  refine ⟨60607761647890467921002275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80810348863853957228003033 60607761647890467921002275)
  ·
    refine ⟨90911642471835701881503413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60607761647890467921002275 90911642471835701881503413)
    ·
      refine ⟨8522966481734597051390945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90911642471835701881503413 8522966481734597051390945)
      ·
        refine ⟨6392224861300947788543209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8522966481734597051390945 6392224861300947788543209)
        ·
          refine ⟨4794168645975710841407407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6392224861300947788543209 4794168645975710841407407)
          ·
            refine ⟨7191252968963566262111111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794168645975710841407407 7191252968963566262111111)
            ·
              refine ⟨10786879453445349393166667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191252968963566262111111 10786879453445349393166667)
              ·
                refine ⟨16180319180168024089750001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10786879453445349393166667 16180319180168024089750001)
                ·
                  refine ⟨12135239385126018067312501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16180319180168024089750001 12135239385126018067312501)
                  ·
                    refine ⟨1137678692355564193810547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12135239385126018067312501 1137678692355564193810547)
                    ·
                      rfl

theorem cell22_3323432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3323432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323432 prefixEnd_3323432 := by exact prefixLift 3323432
  have htrace : WordTrace (prefixWord ++ tailWord_3323432) baseStart_3323432 baseEnd_3323432 := by
    simpa [prefixWord, tailWord_3323432, baseEnd_3323432] using wordTrace_append hprefix tailTrace_3323432
  have hstable : (prefixWord ++ tailWord_3323432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323432).length < 2 ^ (prefixWord ++ tailWord_3323432).sum := by decide
  have hdescent : baseEnd_3323432 < baseStart_3323432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323445 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 6]
def baseStart_3323445 : Nat := 118140960795 + 3323445 * 2 ^ 59
def prefixEnd_3323445 : Nat := 4983230072969 + 3 ^ 40 * 3323445 * 2
def baseEnd_3323445 : Nat := 379227714173745497745169

theorem tailTrace_3323445 : CollatzResearch.WordTrace tailWord_3323445 prefixEnd_3323445 379227714173745497745169 := by
  unfold tailWord_3323445
  simp only [CollatzResearch.WordTrace]
  refine ⟨121215997444733839062227789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80810664963155892708151859 121215997444733839062227789)
  ·
    refine ⟨45455999041775189648335421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121215997444733839062227789 45455999041775189648335421)
    ·
      refine ⟨17045999640665696118125783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45455999041775189648335421 17045999640665696118125783)
      ·
        refine ⟨25568999460998544177188675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17045999640665696118125783 25568999460998544177188675)
        ·
          refine ⟨38353499191497816265783013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25568999460998544177188675 38353499191497816265783013)
          ·
            refine ⟨7191281098405840549834315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38353499191497816265783013 7191281098405840549834315)
            ·
              refine ⟨10786921647608760824751473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191281098405840549834315 10786921647608760824751473)
              ·
                refine ⟨8090191235706570618563605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10786921647608760824751473 8090191235706570618563605)
                ·
                  refine ⟨379227714173745497745169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8090191235706570618563605 379227714173745497745169)
                  ·
                    rfl

theorem cell22_3323445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_3323445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323445 prefixEnd_3323445 := by exact prefixLift 3323445
  have htrace : WordTrace (prefixWord ++ tailWord_3323445) baseStart_3323445 baseEnd_3323445 := by
    simpa [prefixWord, tailWord_3323445, baseEnd_3323445] using wordTrace_append hprefix tailTrace_3323445
  have hstable : (prefixWord ++ tailWord_3323445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323445).length < 2 ^ (prefixWord ++ tailWord_3323445).sum := by decide
  have hdescent : baseEnd_3323445 < baseStart_3323445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323473 : List Nat := [1, 2, 2, 1, 3, 2, 11]
def baseStart_3323473 : Nat := 118140960795 + 3323473 * 2 ^ 59
def prefixEnd_3323473 : Nat := 4983230072969 + 3 ^ 40 * 3323473 * 2
def baseEnd_3323473 : Nat := 42136767684942731612423

theorem tailTrace_3323473 : CollatzResearch.WordTrace tailWord_3323473 prefixEnd_3323473 42136767684942731612423 := by
  unfold tailWord_3323473
  simp only [CollatzResearch.WordTrace]
  refine ⟨121217018688632399844247073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80811345792421599896164715 121217018688632399844247073)
  ·
    refine ⟨90912764016474299883185305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121217018688632399844247073 90912764016474299883185305)
    ·
      refine ⟨68184573012355724912388979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90912764016474299883185305 68184573012355724912388979)
      ·
        refine ⟨102276859518533587368583469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68184573012355724912388979 102276859518533587368583469)
        ·
          refine ⟨38353822319450095263218801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102276859518533587368583469 38353822319450095263218801)
          ·
            refine ⟨28765366739587571447414101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38353822319450095263218801 28765366739587571447414101)
            ·
              refine ⟨42136767684942731612423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28765366739587571447414101 42136767684942731612423)
              ·
                rfl

theorem cell22_3323473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 11].length) (baseStart_3323473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323473 prefixEnd_3323473 := by exact prefixLift 3323473
  have htrace : WordTrace (prefixWord ++ tailWord_3323473) baseStart_3323473 baseEnd_3323473 := by
    simpa [prefixWord, tailWord_3323473, baseEnd_3323473] using wordTrace_append hprefix tailTrace_3323473
  have hstable : (prefixWord ++ tailWord_3323473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323473).length < 2 ^ (prefixWord ++ tailWord_3323473).sum := by decide
  have hdescent : baseEnd_3323473 < baseStart_3323473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323552 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 5]
def baseStart_3323552 : Nat := 118140960795 + 3323552 * 2 ^ 59
def prefixEnd_3323552 : Nat := 4983230072969 + 3 ^ 40 * 3323552 * 2
def baseEnd_3323552 : Nat := 379239923602641293603393

theorem tailTrace_3323552 : CollatzResearch.WordTrace tailWord_3323552 prefixEnd_3323552 379239923602641293603393 := by
  unfold tailWord_3323552
  simp only [CollatzResearch.WordTrace]
  refine ⟨60609950027673098168186455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80813266703564130890915273 60609950027673098168186455)
  ·
    refine ⟨90914925041509647252279683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60609950027673098168186455 90914925041509647252279683)
    ·
      refine ⟨136372387562264470878419525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90914925041509647252279683 136372387562264470878419525)
      ·
        refine ⟨25569822667924588289703661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136372387562264470878419525 25569822667924588289703661)
        ·
          refine ⟨9588683500471720608638873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25569822667924588289703661 9588683500471720608638873)
          ·
            refine ⟨7191512625353790456479155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9588683500471720608638873 7191512625353790456479155)
            ·
              refine ⟨10787268938030685684718733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191512625353790456479155 10787268938030685684718733)
              ·
                refine ⟨4045225851761507131769525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10787268938030685684718733 4045225851761507131769525)
                ·
                  refine ⟨379239923602641293603393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4045225851761507131769525 379239923602641293603393)
                  ·
                    rfl

theorem cell22_3323552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_3323552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323552 prefixEnd_3323552 := by exact prefixLift 3323552
  have htrace : WordTrace (prefixWord ++ tailWord_3323552) baseStart_3323552 baseEnd_3323552 := by
    simpa [prefixWord, tailWord_3323552, baseEnd_3323552] using wordTrace_append hprefix tailTrace_3323552
  have hstable : (prefixWord ++ tailWord_3323552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323552).length < 2 ^ (prefixWord ++ tailWord_3323552).sum := by decide
  have hdescent : baseEnd_3323552 < baseStart_3323552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323590 : List Nat := [6, 1, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3323590 : Nat := 118140960795 + 3323590 * 2 ^ 59
def prefixEnd_3323590 : Nat := 4983230072969 + 3 ^ 40 * 3323590 * 2
def baseEnd_3323590 : Nat := 1137732778984504448360063

theorem tailTrace_3323590 : CollatzResearch.WordTrace tailWord_3323590 prefixEnd_3323590 1137732778984504448360063 := by
  unfold tailWord_3323590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788165188412766525820507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80814190686139019217504149 3788165188412766525820507)
  ·
    refine ⟨5682247782619149788730761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788165188412766525820507 5682247782619149788730761)
    ·
      refine ⟨4261685836964362341548071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5682247782619149788730761 4261685836964362341548071)
      ·
        refine ⟨6392528755446543512322107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4261685836964362341548071 6392528755446543512322107)
        ·
          refine ⟨9588793133169815268483161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6392528755446543512322107 9588793133169815268483161)
          ·
            refine ⟨7191594849877361451362371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9588793133169815268483161 7191594849877361451362371)
            ·
              refine ⟨10787392274816042177043557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191594849877361451362371 10787392274816042177043557)
              ·
                refine ⟨2022636051528007908195667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10787392274816042177043557 2022636051528007908195667)
                ·
                  refine ⟨3033954077292011862293501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022636051528007908195667 3033954077292011862293501)
                  ·
                    refine ⟨1137732778984504448360063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3033954077292011862293501 1137732778984504448360063)
                    ·
                      rfl

theorem cell22_3323590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3323590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323590 prefixEnd_3323590 := by exact prefixLift 3323590
  have htrace : WordTrace (prefixWord ++ tailWord_3323590) baseStart_3323590 baseEnd_3323590 := by
    simpa [prefixWord, tailWord_3323590, baseEnd_3323590] using wordTrace_append hprefix tailTrace_3323590
  have hstable : (prefixWord ++ tailWord_3323590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323590).length < 2 ^ (prefixWord ++ tailWord_3323590).sum := by decide
  have hdescent : baseEnd_3323590 < baseStart_3323590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323627 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 2, 4]
def baseStart_3323627 : Nat := 118140960795 + 3323627 * 2 ^ 59
def prefixEnd_3323627 : Nat := 4983230072969 + 3 ^ 40 * 3323627 * 2
def baseEnd_3323627 : Nat := 1137745444840648685184949

theorem tailTrace_3323627 : CollatzResearch.WordTrace tailWord_3323627 prefixEnd_3323627 1137745444840648685184949 := by
  unfold tailWord_3323627
  simp only [CollatzResearch.WordTrace]
  refine ⟨121222635530074484145353135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80815090353382989430235423 121222635530074484145353135)
  ·
    refine ⟨181833953295111726218029703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121222635530074484145353135 181833953295111726218029703)
    ·
      refine ⟨272750929942667589327044555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181833953295111726218029703 272750929942667589327044555)
      ·
        refine ⟨409126394914001383990566833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272750929942667589327044555 409126394914001383990566833)
        ·
          refine ⟨306844796185501037992925125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409126394914001383990566833 306844796185501037992925125)
          ·
            refine ⟨57533399284781444623673461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306844796185501037992925125 57533399284781444623673461)
            ·
              refine ⟨5393756182948260433469387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57533399284781444623673461 5393756182948260433469387)
              ·
                refine ⟨8090634274422390650204081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393756182948260433469387 8090634274422390650204081)
                ·
                  refine ⟨6067975705816792987653061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8090634274422390650204081 6067975705816792987653061)
                  ·
                    refine ⟨1137745444840648685184949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6067975705816792987653061 1137745444840648685184949)
                    ·
                      rfl

theorem cell22_3323627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4].length) (baseStart_3323627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323627 prefixEnd_3323627 := by exact prefixLift 3323627
  have htrace : WordTrace (prefixWord ++ tailWord_3323627) baseStart_3323627 baseEnd_3323627 := by
    simpa [prefixWord, tailWord_3323627, baseEnd_3323627] using wordTrace_append hprefix tailTrace_3323627
  have hstable : (prefixWord ++ tailWord_3323627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323627).length < 2 ^ (prefixWord ++ tailWord_3323627).sum := by decide
  have hdescent : baseEnd_3323627 < baseStart_3323627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323646 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_3323646 : Nat := 118140960795 + 3323646 * 2 ^ 59
def prefixEnd_3323646 : Nat := 4983230072969 + 3 ^ 40 * 3323646 * 2
def baseEnd_3323646 : Nat := 1137751948928938968959891

theorem tailTrace_3323646 : CollatzResearch.WordTrace tailWord_3323646 prefixEnd_3323646 1137751948928938968959891 := by
  unfold tailWord_3323646
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152916064625706298786849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80815552344670433593529861 15152916064625706298786849)
  ·
    refine ⟨11364687048469279724090137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15152916064625706298786849 11364687048469279724090137)
    ·
      refine ⟨8523515286351959793067603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11364687048469279724090137 8523515286351959793067603)
      ·
        refine ⟨12785272929527939689601405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523515286351959793067603 12785272929527939689601405)
        ·
          refine ⟨4794477348572977383600527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12785272929527939689601405 4794477348572977383600527)
          ·
            refine ⟨7191716022859466075400791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794477348572977383600527 7191716022859466075400791)
            ·
              refine ⟨10787574034289199113101187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191716022859466075400791 10787574034289199113101187)
              ·
                refine ⟨16181361051433798669651781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10787574034289199113101187 16181361051433798669651781)
                ·
                  refine ⟨3034005197143837250559709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16181361051433798669651781 3034005197143837250559709)
                  ·
                    refine ⟨1137751948928938968959891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034005197143837250559709 1137751948928938968959891)
                    ·
                      rfl

theorem cell22_3323646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_3323646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323646 prefixEnd_3323646 := by exact prefixLift 3323646
  have htrace : WordTrace (prefixWord ++ tailWord_3323646) baseStart_3323646 baseEnd_3323646 := by
    simpa [prefixWord, tailWord_3323646, baseEnd_3323646] using wordTrace_append hprefix tailTrace_3323646
  have hstable : (prefixWord ++ tailWord_3323646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323646).length < 2 ^ (prefixWord ++ tailWord_3323646).sum := by decide
  have hdescent : baseEnd_3323646 < baseStart_3323646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323674 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_3323674 : Nat := 118140960795 + 3323674 * 2 ^ 59
def prefixEnd_3323674 : Nat := 4983230072969 + 3 ^ 40 * 3323674 * 2
def baseEnd_3323674 : Nat := 1137761533901156229259805

theorem tailTrace_3323674 : CollatzResearch.WordTrace tailWord_3323674 prefixEnd_3323674 1137761533901156229259805 := by
  unfold tailWord_3323674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30306087440226052793078519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80816233173936140781542717 30306087440226052793078519)
  ·
    refine ⟨45459131160339079189617779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30306087440226052793078519 45459131160339079189617779)
    ·
      refine ⟨68188696740508618784426669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45459131160339079189617779 68188696740508618784426669)
      ·
        refine ⟨25570761277690732044160001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68188696740508618784426669 25570761277690732044160001)
        ·
          refine ⟨19178070958268049033120001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25570761277690732044160001 19178070958268049033120001)
          ·
            refine ⟨14383553218701036774840001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19178070958268049033120001 14383553218701036774840001)
            ·
              refine ⟨10787664914025777581130001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14383553218701036774840001 10787664914025777581130001)
              ·
                refine ⟨8090748685519333185847501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10787664914025777581130001 8090748685519333185847501)
                ·
                  refine ⟨3034030757069749944692813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8090748685519333185847501 3034030757069749944692813)
                  ·
                    refine ⟨1137761533901156229259805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034030757069749944692813 1137761533901156229259805)
                    ·
                      rfl

theorem cell22_3323674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_3323674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323674 prefixEnd_3323674 := by exact prefixLift 3323674
  have htrace : WordTrace (prefixWord ++ tailWord_3323674) baseStart_3323674 baseEnd_3323674 := by
    simpa [prefixWord, tailWord_3323674, baseEnd_3323674] using wordTrace_append hprefix tailTrace_3323674
  have hstable : (prefixWord ++ tailWord_3323674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323674).length < 2 ^ (prefixWord ++ tailWord_3323674).sum := by decide
  have hdescent : baseEnd_3323674 < baseStart_3323674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323717 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_3323717 : Nat := 118140960795 + 3323717 * 2 ^ 59
def prefixEnd_3323717 : Nat := 4983230072969 + 3 ^ 40 * 3323717 * 2
def baseEnd_3323717 : Nat := 1137776253679918450434673

theorem tailTrace_3323717 : CollatzResearch.WordTrace tailWord_3323717 prefixEnd_3323717 1137776253679918450434673 := by
  unfold tailWord_3323717
  simp only [CollatzResearch.WordTrace]
  refine ⟨121225918099748429516129405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80817278733165619677419603 121225918099748429516129405)
  ·
    refine ⟨45459719287405661068548527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121225918099748429516129405 45459719287405661068548527)
    ·
      refine ⟨68189578931108491602822791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45459719287405661068548527 68189578931108491602822791)
      ·
        refine ⟨102284368396662737404234187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68189578931108491602822791 102284368396662737404234187)
        ·
          refine ⟨153426552594994106106351281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102284368396662737404234187 153426552594994106106351281)
          ·
            refine ⟨115069914446245579579763461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153426552594994106106351281 115069914446245579579763461)
            ·
              refine ⟨21575608958671046171205649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115069914446245579579763461 21575608958671046171205649)
              ·
                refine ⟨16181706719003284628404237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21575608958671046171205649 16181706719003284628404237)
                ·
                  refine ⟨6068140019626231735651589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16181706719003284628404237 6068140019626231735651589)
                  ·
                    refine ⟨1137776253679918450434673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6068140019626231735651589 1137776253679918450434673)
                    ·
                      rfl

theorem cell22_3323717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_3323717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323717 prefixEnd_3323717 := by exact prefixLift 3323717
  have htrace : WordTrace (prefixWord ++ tailWord_3323717) baseStart_3323717 baseEnd_3323717 := by
    simpa [prefixWord, tailWord_3323717, baseEnd_3323717] using wordTrace_append hprefix tailTrace_3323717
  have hstable : (prefixWord ++ tailWord_3323717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323717).length < 2 ^ (prefixWord ++ tailWord_3323717).sum := by decide
  have hdescent : baseEnd_3323717 < baseStart_3323717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323749 : List Nat := [1, 3, 1, 3, 1, 1, 1, 7, 4]
def baseStart_3323749 : Nat := 118140960795 + 3323749 * 2 ^ 59
def prefixEnd_3323749 : Nat := 4983230072969 + 3 ^ 40 * 3323749 * 2
def baseEnd_3323749 : Nat := 379262402644627011211525

theorem tailTrace_3323749 : CollatzResearch.WordTrace tailWord_3323749 prefixEnd_3323749 379262402644627011211525 := by
  unfold tailWord_3323749
  simp only [CollatzResearch.WordTrace]
  refine ⟨121227085235632498981294301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80818056823754999320862867 121227085235632498981294301)
  ·
    refine ⟨45460156963362187117985363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121227085235632498981294301 45460156963362187117985363)
    ·
      refine ⟨68190235445043280676978045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45460156963362187117985363 68190235445043280676978045)
      ·
        refine ⟨25571338291891230253866767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68190235445043280676978045 25571338291891230253866767)
        ·
          refine ⟨38357007437836845380800151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25571338291891230253866767 38357007437836845380800151)
          ·
            refine ⟨57535511156755268071200227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38357007437836845380800151 57535511156755268071200227)
            ·
              refine ⟨86303266735132902106800341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57535511156755268071200227 86303266735132902106800341)
              ·
                refine ⟨2022732814104677393128133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86303266735132902106800341 2022732814104677393128133)
                ·
                  refine ⟨379262402644627011211525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2022732814104677393128133 379262402644627011211525)
                  ·
                    rfl

theorem cell22_3323749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_3323749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323749 prefixEnd_3323749 := by exact prefixLift 3323749
  have htrace : WordTrace (prefixWord ++ tailWord_3323749) baseStart_3323749 baseEnd_3323749 := by
    simpa [prefixWord, tailWord_3323749, baseEnd_3323749] using wordTrace_append hprefix tailTrace_3323749
  have hstable : (prefixWord ++ tailWord_3323749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323749).length < 2 ^ (prefixWord ++ tailWord_3323749).sum := by decide
  have hdescent : baseEnd_3323749 < baseStart_3323749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323751 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3323751 : Nat := 118140960795 + 3323751 * 2 ^ 59
def prefixEnd_3323751 : Nat := 4983230072969 + 3 ^ 40 * 3323751 * 2
def baseEnd_3323751 : Nat := 1137787892574753695084569

theorem tailTrace_3323751 : CollatzResearch.WordTrace tailWord_3323751 prefixEnd_3323751 1137787892574753695084569 := by
  unfold tailWord_3323751
  simp only [CollatzResearch.WordTrace]
  refine ⟨121227158181625253322867107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80818105454416835548578071 121227158181625253322867107)
  ·
    refine ⟨181840737272437879984300661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121227158181625253322867107 181840737272437879984300661)
    ·
      refine ⟨17047569119291051248528187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181840737272437879984300661 17047569119291051248528187)
      ·
        refine ⟨25571353678936576872792281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17047569119291051248528187 25571353678936576872792281)
        ·
          refine ⟨19178515259202432654594211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25571353678936576872792281 19178515259202432654594211)
          ·
            refine ⟨28767772888803648981891317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19178515259202432654594211 28767772888803648981891317)
            ·
              refine ⟨2696978708325342092052311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28767772888803648981891317 2696978708325342092052311)
              ·
                refine ⟨4045468062488013138078467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696978708325342092052311 4045468062488013138078467)
                ·
                  refine ⟨6068202093732019707117701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045468062488013138078467 6068202093732019707117701)
                  ·
                    refine ⟨1137787892574753695084569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6068202093732019707117701 1137787892574753695084569)
                    ·
                      rfl

theorem cell22_3323751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3323751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323751 prefixEnd_3323751 := by exact prefixLift 3323751
  have htrace : WordTrace (prefixWord ++ tailWord_3323751) baseStart_3323751 baseEnd_3323751 := by
    simpa [prefixWord, tailWord_3323751, baseEnd_3323751] using wordTrace_append hprefix tailTrace_3323751
  have hstable : (prefixWord ++ tailWord_3323751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323751).length < 2 ^ (prefixWord ++ tailWord_3323751).sum := by decide
  have hdescent : baseEnd_3323751 < baseStart_3323751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323762 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_3323762 : Nat := 118140960795 + 3323762 * 2 ^ 59
def prefixEnd_3323762 : Nat := 4983230072969 + 3 ^ 40 * 3323762 * 2
def baseEnd_3323762 : Nat := 1137791658099553333059535

theorem tailTrace_3323762 : CollatzResearch.WordTrace tailWord_3323762 prefixEnd_3323762 1137791658099553333059535 := by
  unfold tailWord_3323762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30306889846146350550379385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80818372923056934801011693 30306889846146350550379385)
  ·
    refine ⟨22730167384609762912784539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30306889846146350550379385 22730167384609762912784539)
    ·
      refine ⟨34095251076914644369176809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22730167384609762912784539 34095251076914644369176809)
      ·
        refine ⟨25571438307685983276882607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34095251076914644369176809 25571438307685983276882607)
        ·
          refine ⟨38357157461528974915323911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25571438307685983276882607 38357157461528974915323911)
          ·
            refine ⟨57535736192293462372985867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38357157461528974915323911 57535736192293462372985867)
            ·
              refine ⟨86303604288440193559478801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57535736192293462372985867 86303604288440193559478801)
              ·
                refine ⟨64727703216330145169609101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86303604288440193559478801 64727703216330145169609101)
                ·
                  refine ⟨24272888706123804438603413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64727703216330145169609101 24272888706123804438603413)
                  ·
                    refine ⟨1137791658099553333059535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24272888706123804438603413 1137791658099553333059535)
                    ·
                      rfl

theorem cell22_3323762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_3323762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323762 prefixEnd_3323762 := by exact prefixLift 3323762
  have htrace : WordTrace (prefixWord ++ tailWord_3323762) baseStart_3323762 baseEnd_3323762 := by
    simpa [prefixWord, tailWord_3323762, baseEnd_3323762] using wordTrace_append hprefix tailTrace_3323762
  have hstable : (prefixWord ++ tailWord_3323762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323762).length < 2 ^ (prefixWord ++ tailWord_3323762).sum := by decide
  have hdescent : baseEnd_3323762 < baseStart_3323762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323796 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3323796 : Nat := 118140960795 + 3323796 * 2 ^ 59
def prefixEnd_3323796 : Nat := 4983230072969 + 3 ^ 40 * 3323796 * 2
def baseEnd_3323796 : Nat := 1137803296994388577709431

theorem tailTrace_3323796 : CollatzResearch.WordTrace tailWord_3323796 prefixEnd_3323796 1137803296994388577709431 := by
  unfold tailWord_3323796
  simp only [CollatzResearch.WordTrace]
  refine ⟨60614399733231113004127621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80819199644308150672170161 60614399733231113004127621)
  ·
    refine ⟨11365199949980833688273929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60614399733231113004127621 11365199949980833688273929)
    ·
      refine ⟨8523899962485625266205447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11365199949980833688273929 8523899962485625266205447)
      ·
        refine ⟨12785849943728437899308171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523899962485625266205447 12785849943728437899308171)
        ·
          refine ⟨19178774915592656848962257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12785849943728437899308171 19178774915592656848962257)
          ·
            refine ⟨14384081186694492636721693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19178774915592656848962257 14384081186694492636721693)
            ·
              refine ⟨5394030445010434738770635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14384081186694492636721693 5394030445010434738770635)
              ·
                refine ⟨8091045667515652108155953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394030445010434738770635 8091045667515652108155953)
                ·
                  refine ⟨6068284250636739081116965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8091045667515652108155953 6068284250636739081116965)
                  ·
                    refine ⟨1137803296994388577709431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6068284250636739081116965 1137803296994388577709431)
                    ·
                      rfl

theorem cell22_3323796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3323796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323796 prefixEnd_3323796 := by exact prefixLift 3323796
  have htrace : WordTrace (prefixWord ++ tailWord_3323796) baseStart_3323796 baseEnd_3323796 := by
    simpa [prefixWord, tailWord_3323796, baseEnd_3323796] using wordTrace_append hprefix tailTrace_3323796
  have hstable : (prefixWord ++ tailWord_3323796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323796).length < 2 ^ (prefixWord ++ tailWord_3323796).sum := by decide
  have hdescent : baseEnd_3323796 < baseStart_3323796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323933 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_3323933 : Nat := 118140960795 + 3323933 * 2 ^ 59
def prefixEnd_3323933 : Nat := 4983230072969 + 3 ^ 40 * 3323933 * 2
def baseEnd_3323933 : Nat := 1137850194894165887034011

theorem tailTrace_3323933 : CollatzResearch.WordTrace tailWord_3323933 prefixEnd_3323933 1137850194894165887034011 := by
  unfold tailWord_3323933
  simp only [CollatzResearch.WordTrace]
  refine ⟨121233796266965898405992453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80822530844643932270661635 121233796266965898405992453)
  ·
    refine ⟨22731336800056105951123585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121233796266965898405992453 22731336800056105951123585)
    ·
      refine ⟨17048502600042079463342689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22731336800056105951123585 17048502600042079463342689)
      ·
        refine ⟨12786376950031559597507017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17048502600042079463342689 12786376950031559597507017)
        ·
          refine ⟨9589782712523669698130263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12786376950031559597507017 9589782712523669698130263)
          ·
            refine ⟨14384674068785504547195395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589782712523669698130263 14384674068785504547195395)
            ·
              refine ⟨21577011103178256820793093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14384674068785504547195395 21577011103178256820793093)
              ·
                refine ⟨4045689581845923153898705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21577011103178256820793093 4045689581845923153898705)
                ·
                  refine ⟨3034267186384442365424029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4045689581845923153898705 3034267186384442365424029)
                  ·
                    refine ⟨1137850194894165887034011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034267186384442365424029 1137850194894165887034011)
                    ·
                      rfl

theorem cell22_3323933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_3323933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323933 prefixEnd_3323933 := by exact prefixLift 3323933
  have htrace : WordTrace (prefixWord ++ tailWord_3323933) baseStart_3323933 baseEnd_3323933 := by
    simpa [prefixWord, tailWord_3323933, baseEnd_3323933] using wordTrace_append hprefix tailTrace_3323933
  have hstable : (prefixWord ++ tailWord_3323933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323933).length < 2 ^ (prefixWord ++ tailWord_3323933).sum := by decide
  have hdescent : baseEnd_3323933 < baseStart_3323933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323946 : List Nat := [3, 1, 4, 1, 2, 1, 3, 7]
def baseStart_3323946 : Nat := 118140960795 + 3323946 * 2 ^ 59
def prefixEnd_3323946 : Nat := 4983230072969 + 3 ^ 40 * 3323946 * 2
def baseEnd_3323946 : Nat := 126428293895537576273219

theorem tailTrace_3323946 : CollatzResearch.WordTrace tailWord_3323946 prefixEnd_3323946 126428293895537576273219 := by
  unfold tailWord_3323946
  simp only [CollatzResearch.WordTrace]
  refine ⟨30308567603979700406553923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80822846943945867750810461 30308567603979700406553923)
  ·
    refine ⟨45462851405969550609830885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30308567603979700406553923 45462851405969550609830885)
    ·
      refine ⟨8524284638619290739343291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45462851405969550609830885 8524284638619290739343291)
      ·
        refine ⟨12786426957928936109014937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524284638619290739343291 12786426957928936109014937)
        ·
          refine ⟨9589820218446702081761203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12786426957928936109014937 9589820218446702081761203)
          ·
            refine ⟨14384730327670053122641805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589820218446702081761203 14384730327670053122641805)
            ·
              refine ⟨5394273872876269920990677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14384730327670053122641805 5394273872876269920990677)
              ·
                refine ⟨126428293895537576273219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5394273872876269920990677 126428293895537576273219)
                ·
                  rfl

theorem cell22_3323946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_3323946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323946 prefixEnd_3323946 := by exact prefixLift 3323946
  have htrace : WordTrace (prefixWord ++ tailWord_3323946) baseStart_3323946 baseEnd_3323946 := by
    simpa [prefixWord, tailWord_3323946, baseEnd_3323946] using wordTrace_append hprefix tailTrace_3323946
  have hstable : (prefixWord ++ tailWord_3323946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323946).length < 2 ^ (prefixWord ++ tailWord_3323946).sum := by decide
  have hdescent : baseEnd_3323946 < baseStart_3323946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323991 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 5]
def baseStart_3323991 : Nat := 118140960795 + 3323991 * 2 ^ 59
def prefixEnd_3323991 : Nat := 4983230072969 + 3 ^ 40 * 3323991 * 2
def baseEnd_3323991 : Nat := 379290016493157689694611

theorem tailTrace_3323991 : CollatzResearch.WordTrace tailWord_3323991 prefixEnd_3323991 379290016493157689694611 := by
  unfold tailWord_3323991
  simp only [CollatzResearch.WordTrace]
  refine ⟨121235911700755774311603827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80823941133837182874402551 121235911700755774311603827)
  ·
    refine ⟨181853867551133661467405741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121235911700755774311603827 181853867551133661467405741)
    ·
      refine ⟨68195200331675123050277153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181853867551133661467405741 68195200331675123050277153)
      ·
        refine ⟨51146400248756342287707865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68195200331675123050277153 51146400248756342287707865)
        ·
          refine ⟨38359800186567256715780899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51146400248756342287707865 38359800186567256715780899)
          ·
            refine ⟨57539700279850885073671349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38359800186567256715780899 57539700279850885073671349)
            ·
              refine ⟨5394346901236020475656689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57539700279850885073671349 5394346901236020475656689)
              ·
                refine ⟨4045760175927015356742517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5394346901236020475656689 4045760175927015356742517)
                ·
                  refine ⟨379290016493157689694611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4045760175927015356742517 379290016493157689694611)
                  ·
                    rfl

theorem cell22_3323991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 5].length) (baseStart_3323991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3323991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3323991 prefixEnd_3323991 := by exact prefixLift 3323991
  have htrace : WordTrace (prefixWord ++ tailWord_3323991) baseStart_3323991 baseEnd_3323991 := by
    simpa [prefixWord, tailWord_3323991, baseEnd_3323991] using wordTrace_append hprefix tailTrace_3323991
  have hstable : (prefixWord ++ tailWord_3323991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323991).length < 2 ^ (prefixWord ++ tailWord_3323991).sum := by decide
  have hdescent : baseEnd_3323991 < baseStart_3323991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324049 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_3324049 : Nat := 118140960795 + 3324049 * 2 ^ 59
def prefixEnd_3324049 : Nat := 4983230072969 + 3 ^ 40 * 3324049 * 2
def baseEnd_3324049 : Nat := 1137889904064780251133655

theorem tailTrace_3324049 : CollatzResearch.WordTrace tailWord_3324049 prefixEnd_3324049 1137889904064780251133655 := by
  unfold tailWord_3324049
  simp only [CollatzResearch.WordTrace]
  refine ⟨121238027134545650217215201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80825351423030433478143467 121238027134545650217215201)
  ·
    refine ⟨90928520350909237662911401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121238027134545650217215201 90928520350909237662911401)
    ·
      refine ⟨68196390263181928247183551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90928520350909237662911401 68196390263181928247183551)
      ·
        refine ⟨102294585394772892370775327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68196390263181928247183551 102294585394772892370775327)
        ·
          refine ⟨153441878092159338556162991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102294585394772892370775327 153441878092159338556162991)
          ·
            refine ⟨230162817138239007834244487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153441878092159338556162991 230162817138239007834244487)
            ·
              refine ⟨345244225707358511751366731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230162817138239007834244487 345244225707358511751366731)
              ·
                refine ⟨517866338561037767627050097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345244225707358511751366731 517866338561037767627050097)
                ·
                  refine ⟨388399753920778325720287573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517866338561037767627050097 388399753920778325720287573)
                  ·
                    refine ⟨1137889904064780251133655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 388399753920778325720287573 1137889904064780251133655)
                    ·
                      rfl

theorem cell22_3324049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_3324049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324049 prefixEnd_3324049 := by exact prefixLift 3324049
  have htrace : WordTrace (prefixWord ++ tailWord_3324049) baseStart_3324049 baseEnd_3324049 := by
    simpa [prefixWord, tailWord_3324049, baseEnd_3324049] using wordTrace_append hprefix tailTrace_3324049
  have hstable : (prefixWord ++ tailWord_3324049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324049).length < 2 ^ (prefixWord ++ tailWord_3324049).sum := by decide
  have hdescent : baseEnd_3324049 < baseStart_3324049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324085 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3324085 : Nat := 118140960795 + 3324085 * 2 ^ 59
def prefixEnd_3324085 : Nat := 4983230072969 + 3 ^ 40 * 3324085 * 2
def baseEnd_3324085 : Nat := 1137902227600488157233545

theorem tailTrace_3324085 : CollatzResearch.WordTrace tailWord_3324085 prefixEnd_3324085 1137902227600488157233545 := by
  unfold tailWord_3324085
  simp only [CollatzResearch.WordTrace]
  refine ⟨121239340162415228365525709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80826226774943485577017139 121239340162415228365525709)
  ·
    refine ⟨45464752560905710637072141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121239340162415228365525709 45464752560905710637072141)
    ·
      refine ⟨17049282210339641488902053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45464752560905710637072141 17049282210339641488902053)
      ·
        refine ⟨3196740414438682779169135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17049282210339641488902053 3196740414438682779169135)
        ·
          refine ⟨4795110621658024168753703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196740414438682779169135 4795110621658024168753703)
          ·
            refine ⟨7192665932487036253130555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795110621658024168753703 7192665932487036253130555)
            ·
              refine ⟨10788998898730554379695833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192665932487036253130555 10788998898730554379695833)
              ·
                refine ⟨8091749174047915784771875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10788998898730554379695833 8091749174047915784771875)
                ·
                  refine ⟨12137623761071873677157813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091749174047915784771875 12137623761071873677157813)
                  ·
                    refine ⟨1137902227600488157233545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12137623761071873677157813 1137902227600488157233545)
                    ·
                      rfl

theorem cell22_3324085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3324085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324085 prefixEnd_3324085 := by exact prefixLift 3324085
  have htrace : WordTrace (prefixWord ++ tailWord_3324085) baseStart_3324085 baseEnd_3324085 := by
    simpa [prefixWord, tailWord_3324085, baseEnd_3324085] using wordTrace_append hprefix tailTrace_3324085
  have hstable : (prefixWord ++ tailWord_3324085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324085).length < 2 ^ (prefixWord ++ tailWord_3324085).sum := by decide
  have hdescent : baseEnd_3324085 < baseStart_3324085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324158 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3324158 : Nat := 118140960795 + 3324158 * 2 ^ 59
def prefixEnd_3324158 : Nat := 4983230072969 + 3 ^ 40 * 3324158 * 2
def baseEnd_3324158 : Nat := 1137927216992340300158321

theorem tailTrace_3324158 : CollatzResearch.WordTrace tailWord_3324158 prefixEnd_3324158 1137927216992340300158321 := by
  unfold tailWord_3324158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15155250336393845229116641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80828001794100507888622085 15155250336393845229116641)
  ·
    refine ⟨11366437752295383921837481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15155250336393845229116641 11366437752295383921837481)
    ·
      refine ⟨8524828314221537941378111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11366437752295383921837481 8524828314221537941378111)
      ·
        refine ⟨12787242471332306912067167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524828314221537941378111 12787242471332306912067167)
        ·
          refine ⟨19180863706998460368100751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12787242471332306912067167 19180863706998460368100751)
          ·
            refine ⟨28771295560497690552151127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19180863706998460368100751 28771295560497690552151127)
            ·
              refine ⟨43156943340746535828226691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28771295560497690552151127 43156943340746535828226691)
              ·
                refine ⟨64735415011119803742340037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43156943340746535828226691 64735415011119803742340037)
                ·
                  refine ⟨12137890314584963201688757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64735415011119803742340037 12137890314584963201688757)
                  ·
                    refine ⟨1137927216992340300158321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12137890314584963201688757 1137927216992340300158321)
                    ·
                      rfl

theorem cell22_3324158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3324158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324158 prefixEnd_3324158 := by exact prefixLift 3324158
  have htrace : WordTrace (prefixWord ++ tailWord_3324158) baseStart_3324158 baseEnd_3324158 := by
    simpa [prefixWord, tailWord_3324158, baseEnd_3324158] using wordTrace_append hprefix tailTrace_3324158
  have hstable : (prefixWord ++ tailWord_3324158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324158).length < 2 ^ (prefixWord ++ tailWord_3324158).sum := by decide
  have hdescent : baseEnd_3324158 < baseStart_3324158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324216 : List Nat := [2, 1, 2, 1, 3, 1, 12]
def baseStart_3324216 : Nat := 118140960795 + 3324216 * 2 ^ 59
def prefixEnd_3324216 : Nat := 4983230072969 + 3 ^ 40 * 3324216 * 2
def baseEnd_3324216 : Nat := 42146187836209166007709

theorem tailTrace_3324216 : CollatzResearch.WordTrace tailWord_3324216 prefixEnd_3324216 42146187836209166007709 := by
  unfold tailWord_3324216
  simp only [CollatzResearch.WordTrace]
  refine ⟨60622059062470318869272251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80829412083293758492363001 60622059062470318869272251)
  ·
    refine ⟨90933088593705478303908377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60622059062470318869272251 90933088593705478303908377)
    ·
      refine ⟨68199816445279108727931283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90933088593705478303908377 68199816445279108727931283)
      ·
        refine ⟨102299724667918663091896925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68199816445279108727931283 102299724667918663091896925)
        ·
          refine ⟨38362396750469498659461347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102299724667918663091896925 38362396750469498659461347)
          ·
            refine ⟨57543595125704247989192021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38362396750469498659461347 57543595125704247989192021)
            ·
              refine ⟨42146187836209166007709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 57543595125704247989192021 42146187836209166007709)
              ·
                rfl

theorem cell22_3324216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 12].length) (baseStart_3324216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324216 prefixEnd_3324216 := by exact prefixLift 3324216
  have htrace : WordTrace (prefixWord ++ tailWord_3324216) baseStart_3324216 baseEnd_3324216 := by
    simpa [prefixWord, tailWord_3324216, baseEnd_3324216] using wordTrace_append hprefix tailTrace_3324216
  have hstable : (prefixWord ++ tailWord_3324216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324216).length < 2 ^ (prefixWord ++ tailWord_3324216).sum := by decide
  have hdescent : baseEnd_3324216 < baseStart_3324216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324218 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_3324218 : Nat := 118140960795 + 3324218 * 2 ^ 59
def prefixEnd_3324218 : Nat := 4983230072969 + 3 ^ 40 * 3324218 * 2
def baseEnd_3324218 : Nat := 1137947756218520143658137

theorem tailTrace_3324218 : CollatzResearch.WordTrace tailWord_3324218 prefixEnd_3324218 1137947756218520143658137 := by
  unfold tailWord_3324218
  simp only [CollatzResearch.WordTrace]
  refine ⟨30311047767733348020029327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80829460713955594720078205 30311047767733348020029327)
  ·
    refine ⟨45466571651600022030043991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30311047767733348020029327 45466571651600022030043991)
    ·
      refine ⟨68199857477400033045065987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45466571651600022030043991 68199857477400033045065987)
      ·
        refine ⟨102299786216100049567598981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68199857477400033045065987 102299786216100049567598981)
        ·
          refine ⟨19181209915518759293924809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102299786216100049567598981 19181209915518759293924809)
          ·
            refine ⟨14385907436639069470443607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19181209915518759293924809 14385907436639069470443607)
            ·
              refine ⟨21578861154958604205665411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14385907436639069470443607 21578861154958604205665411)
              ·
                refine ⟨32368291732437906308498117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21578861154958604205665411 32368291732437906308498117)
                ·
                  refine ⟨6069054699832107432843397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32368291732437906308498117 6069054699832107432843397)
                  ·
                    refine ⟨1137947756218520143658137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6069054699832107432843397 1137947756218520143658137)
                    ·
                      rfl

theorem cell22_3324218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_3324218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324218 prefixEnd_3324218 := by exact prefixLift 3324218
  have htrace : WordTrace (prefixWord ++ tailWord_3324218) baseStart_3324218 baseEnd_3324218 := by
    simpa [prefixWord, tailWord_3324218, baseEnd_3324218] using wordTrace_append hprefix tailTrace_3324218
  have hstable : (prefixWord ++ tailWord_3324218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324218).length < 2 ^ (prefixWord ++ tailWord_3324218).sum := by decide
  have hdescent : baseEnd_3324218 < baseStart_3324218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324220 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_3324220 : Nat := 118140960795 + 3324220 * 2 ^ 59
def prefixEnd_3324220 : Nat := 4983230072969 + 3 ^ 40 * 3324220 * 2
def baseEnd_3324220 : Nat := 1137948440859392805108131

theorem tailTrace_3324220 : CollatzResearch.WordTrace tailWord_3324220 prefixEnd_3324220 1137948440859392805108131 := by
  unfold tailWord_3324220
  simp only [CollatzResearch.WordTrace]
  refine ⟨60622132008463073210845057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80829509344617430947793409 60622132008463073210845057)
  ·
    refine ⟨45466599006347304908133793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60622132008463073210845057 45466599006347304908133793)
    ·
      refine ⟨34099949254760478681100345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45466599006347304908133793 34099949254760478681100345)
      ·
        refine ⟨25574961941070359010825259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34099949254760478681100345 25574961941070359010825259)
        ·
          refine ⟨38362442911605538516237889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25574961941070359010825259 38362442911605538516237889)
          ·
            refine ⟨28771832183704153887178417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38362442911605538516237889 28771832183704153887178417)
            ·
              refine ⟨21578874137778115415383813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28771832183704153887178417 21578874137778115415383813)
              ·
                refine ⟨4046038900833396640384465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21578874137778115415383813 4046038900833396640384465)
                ·
                  refine ⟨3034529175625047480288349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4046038900833396640384465 3034529175625047480288349)
                  ·
                    refine ⟨1137948440859392805108131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034529175625047480288349 1137948440859392805108131)
                    ·
                      rfl

theorem cell22_3324220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_3324220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324220 prefixEnd_3324220 := by exact prefixLift 3324220
  have htrace : WordTrace (prefixWord ++ tailWord_3324220) baseStart_3324220 baseEnd_3324220 := by
    simpa [prefixWord, tailWord_3324220, baseEnd_3324220] using wordTrace_append hprefix tailTrace_3324220
  have hstable : (prefixWord ++ tailWord_3324220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324220).length < 2 ^ (prefixWord ++ tailWord_3324220).sum := by decide
  have hdescent : baseEnd_3324220 < baseStart_3324220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324325 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_3324325 : Nat := 118140960795 + 3324325 * 2 ^ 59
def prefixEnd_3324325 : Nat := 4983230072969 + 3 ^ 40 * 3324325 * 2
def baseEnd_3324325 : Nat := 1137984384505207531232809

theorem tailTrace_3324325 : CollatzResearch.WordTrace tailWord_3324325 prefixEnd_3324325 1137984384505207531232809 := by
  unfold tailWord_3324325
  simp only [CollatzResearch.WordTrace]
  refine ⟨121248093681545749354262429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80832062454363832902841619 121248093681545749354262429)
  ·
    refine ⟨45468035130579656007848411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121248093681545749354262429 45468035130579656007848411)
    ·
      refine ⟨68202052695869484011772617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45468035130579656007848411 68202052695869484011772617)
      ·
        refine ⟨51151539521902113008829463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68202052695869484011772617 51151539521902113008829463)
        ·
          refine ⟨76727309282853169513244195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51151539521902113008829463 76727309282853169513244195)
          ·
            refine ⟨115090963924279754269866293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76727309282853169513244195 115090963924279754269866293)
            ·
              refine ⟨10789777867901226962799965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115090963924279754269866293 10789777867901226962799965)
              ·
                refine ⟨4046166700462960111049987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10789777867901226962799965 4046166700462960111049987)
                ·
                  refine ⟨6069250050694440166574981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046166700462960111049987 6069250050694440166574981)
                  ·
                    refine ⟨1137984384505207531232809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6069250050694440166574981 1137984384505207531232809)
                    ·
                      rfl

theorem cell22_3324325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_3324325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324325 prefixEnd_3324325 := by exact prefixLift 3324325
  have htrace : WordTrace (prefixWord ++ tailWord_3324325) baseStart_3324325 baseEnd_3324325 := by
    simpa [prefixWord, tailWord_3324325, baseEnd_3324325] using wordTrace_append hprefix tailTrace_3324325
  have hstable : (prefixWord ++ tailWord_3324325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324325).length < 2 ^ (prefixWord ++ tailWord_3324325).sum := by decide
  have hdescent : baseEnd_3324325 < baseStart_3324325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324372 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3324372 : Nat := 118140960795 + 3324372 * 2 ^ 59
def prefixEnd_3324372 : Nat := 4983230072969 + 3 ^ 40 * 3324372 * 2
def baseEnd_3324372 : Nat := 1138000473565715075307665

theorem tailTrace_3324372 : CollatzResearch.WordTrace tailWord_3324372 prefixEnd_3324372 1138000473565715075307665 := by
  unfold tailWord_3324372
  simp only [CollatzResearch.WordTrace]
  refine ⟨60624903956187738190611685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80833205274916984254148913 60624903956187738190611685)
  ·
    refine ⟨11367169491785200910739691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60624903956187738190611685 11367169491785200910739691)
    ·
      refine ⟨17050754237677801366109537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367169491785200910739691 17050754237677801366109537)
      ·
        refine ⟨12788065678258351024582153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17050754237677801366109537 12788065678258351024582153)
        ·
          refine ⟨9591049258693763268436615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12788065678258351024582153 9591049258693763268436615)
          ·
            refine ⟨14386573888040644902654923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9591049258693763268436615 14386573888040644902654923)
            ·
              refine ⟨21579860832060967353982385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14386573888040644902654923 21579860832060967353982385)
              ·
                refine ⟨16184895624045725515486789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21579860832060967353982385 16184895624045725515486789)
                ·
                  refine ⟨3034667929508573534153773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16184895624045725515486789 3034667929508573534153773)
                  ·
                    refine ⟨1138000473565715075307665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034667929508573534153773 1138000473565715075307665)
                    ·
                      rfl

theorem cell22_3324372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3324372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324372 prefixEnd_3324372 := by exact prefixLift 3324372
  have htrace : WordTrace (prefixWord ++ tailWord_3324372) baseStart_3324372 baseEnd_3324372 := by
    simpa [prefixWord, tailWord_3324372, baseEnd_3324372] using wordTrace_append hprefix tailTrace_3324372
  have hstable : (prefixWord ++ tailWord_3324372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324372).length < 2 ^ (prefixWord ++ tailWord_3324372).sum := by decide
  have hdescent : baseEnd_3324372 < baseStart_3324372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324387 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 2, 4]
def baseStart_3324387 : Nat := 118140960795 + 3324387 * 2 ^ 59
def prefixEnd_3324387 : Nat := 4983230072969 + 3 ^ 40 * 3324387 * 2
def baseEnd_3324387 : Nat := 1138005608372260036182619

theorem tailTrace_3324387 : CollatzResearch.WordTrace tailWord_3324387 prefixEnd_3324387 1138005608372260036182619 := by
  unfold tailWord_3324387
  simp only [CollatzResearch.WordTrace]
  refine ⟨121250355007321133943019415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80833570004880755962012943 121250355007321133943019415)
  ·
    refine ⟨181875532510981700914529123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121250355007321133943019415 181875532510981700914529123)
    ·
      refine ⟨272813298766472551371793685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181875532510981700914529123 272813298766472551371793685)
      ·
        refine ⟨12788123379678400845552829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272813298766472551371793685 12788123379678400845552829)
        ·
          refine ⟨4795546267379400317082311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12788123379678400845552829 4795546267379400317082311)
          ·
            refine ⟨7193319401069100475623467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795546267379400317082311 7193319401069100475623467)
            ·
              refine ⟨10789979101603650713435201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7193319401069100475623467 10789979101603650713435201)
              ·
                refine ⟨8092484326202738035076401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10789979101603650713435201 8092484326202738035076401)
                ·
                  refine ⟨6069363244652053526307301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8092484326202738035076401 6069363244652053526307301)
                  ·
                    refine ⟨1138005608372260036182619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6069363244652053526307301 1138005608372260036182619)
                    ·
                      rfl

theorem cell22_3324387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4].length) (baseStart_3324387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324387 prefixEnd_3324387 := by exact prefixLift 3324387
  have htrace : WordTrace (prefixWord ++ tailWord_3324387) baseStart_3324387 baseEnd_3324387 := by
    simpa [prefixWord, tailWord_3324387, baseEnd_3324387] using wordTrace_append hprefix tailTrace_3324387
  have hstable : (prefixWord ++ tailWord_3324387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324387).length < 2 ^ (prefixWord ++ tailWord_3324387).sum := by decide
  have hdescent : baseEnd_3324387 < baseStart_3324387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324402 : List Nat := [3, 2, 1, 4, 2, 1, 2, 7]
def baseStart_3324402 : Nat := 118140960795 + 3324402 * 2 ^ 59
def prefixEnd_3324402 : Nat := 4983230072969 + 3 ^ 40 * 3324402 * 2
def baseEnd_3324402 : Nat := 126445638130978333006397

theorem tailTrace_3324402 : CollatzResearch.WordTrace tailWord_3324402 prefixEnd_3324402 126445638130978333006397 := by
  unfold tailWord_3324402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30312725525566697876203865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80833934734844527669876973 30312725525566697876203865)
  ·
    refine ⟨22734544144175023407152899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30312725525566697876203865 22734544144175023407152899)
    ·
      refine ⟨34101816216262535110729349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22734544144175023407152899 34101816216262535110729349)
      ·
        refine ⟨6394090540549225333261753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34101816216262535110729349 6394090540549225333261753)
        ·
          refine ⟨4795567905411918999946315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6394090540549225333261753 4795567905411918999946315)
          ·
            refine ⟨7193351858117878499919473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795567905411918999946315 7193351858117878499919473)
            ·
              refine ⟨5395013893588408874939605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7193351858117878499919473 5395013893588408874939605)
              ·
                refine ⟨126445638130978333006397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5395013893588408874939605 126445638130978333006397)
                ·
                  rfl

theorem cell22_3324402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_3324402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324402 prefixEnd_3324402 := by exact prefixLift 3324402
  have htrace : WordTrace (prefixWord ++ tailWord_3324402) baseStart_3324402 baseEnd_3324402 := by
    simpa [prefixWord, tailWord_3324402, baseEnd_3324402] using wordTrace_append hprefix tailTrace_3324402
  have hstable : (prefixWord ++ tailWord_3324402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324402).length < 2 ^ (prefixWord ++ tailWord_3324402).sum := by decide
  have hdescent : baseEnd_3324402 < baseStart_3324402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324451 : List Nat := [1, 1, 1, 4, 4, 1, 4, 2, 1, 3]
def baseStart_3324451 : Nat := 118140960795 + 3324451 * 2 ^ 59
def prefixEnd_3324451 : Nat := 4983230072969 + 3 ^ 40 * 3324451 * 2
def baseEnd_3324451 : Nat := 1138027516880185202582423

theorem tailTrace_3324451 : CollatzResearch.WordTrace tailWord_3324451 prefixEnd_3324451 1138027516880185202582423 := by
  unfold tailWord_3324451
  simp only [CollatzResearch.WordTrace]
  refine ⟨121252689279089272873349207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80835126186059515248899471 121252689279089272873349207)
  ·
    refine ⟨181879033918633909310023811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121252689279089272873349207 181879033918633909310023811)
    ·
      refine ⟨272818550877950863965035717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181879033918633909310023811 272818550877950863965035717)
      ·
        refine ⟨51153478289615786993444197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272818550877950863965035717 51153478289615786993444197)
        ·
          refine ⟨9591277179302960061270787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51153478289615786993444197 9591277179302960061270787)
          ·
            refine ⟨14386915768954440091906181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9591277179302960061270787 14386915768954440091906181)
            ·
              refine ⟨2697546706678957517232409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14386915768954440091906181 2697546706678957517232409)
              ·
                refine ⟨2023160030009218137924307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697546706678957517232409 2023160030009218137924307)
                ·
                  refine ⟨3034740045013827206886461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023160030009218137924307 3034740045013827206886461)
                  ·
                    refine ⟨1138027516880185202582423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034740045013827206886461 1138027516880185202582423)
                    ·
                      rfl

theorem cell22_3324451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 3].length) (baseStart_3324451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324451 prefixEnd_3324451 := by exact prefixLift 3324451
  have htrace : WordTrace (prefixWord ++ tailWord_3324451) baseStart_3324451 baseEnd_3324451 := by
    simpa [prefixWord, tailWord_3324451, baseEnd_3324451] using wordTrace_append hprefix tailTrace_3324451
  have hstable : (prefixWord ++ tailWord_3324451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324451).length < 2 ^ (prefixWord ++ tailWord_3324451).sum := by decide
  have hdescent : baseEnd_3324451 < baseStart_3324451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324477 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_3324477 : Nat := 118140960795 + 3324477 * 2 ^ 59
def prefixEnd_3324477 : Nat := 4983230072969 + 3 ^ 40 * 3324477 * 2
def baseEnd_3324477 : Nat := 1138036417211529801432343

theorem tailTrace_3324477 : CollatzResearch.WordTrace tailWord_3324477 prefixEnd_3324477 1138036417211529801432343 := by
  unfold tailWord_3324477
  simp only [CollatzResearch.WordTrace]
  refine ⟨121253637576995079313795685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80835758384663386209197123 121253637576995079313795685)
  ·
    refine ⟨22735057045686577371336691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121253637576995079313795685 22735057045686577371336691)
    ·
      refine ⟨34102585568529866057005037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22735057045686577371336691 34102585568529866057005037)
      ·
        refine ⟨12788469588198699771376889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34102585568529866057005037 12788469588198699771376889)
        ·
          refine ⟨9591352191149024828532667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12788469588198699771376889 9591352191149024828532667)
          ·
            refine ⟨14387028286723537242799001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9591352191149024828532667 14387028286723537242799001)
            ·
              refine ⟨10790271215042652932099251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14387028286723537242799001 10790271215042652932099251)
              ·
                refine ⟨16185406822563979398148877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10790271215042652932099251 16185406822563979398148877)
                ·
                  refine ⟨6069527558461492274305829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16185406822563979398148877 6069527558461492274305829)
                  ·
                    refine ⟨1138036417211529801432343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6069527558461492274305829 1138036417211529801432343)
                    ·
                      rfl

theorem cell22_3324477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_3324477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324477 prefixEnd_3324477 := by exact prefixLift 3324477
  have htrace : WordTrace (prefixWord ++ tailWord_3324477) baseStart_3324477 baseEnd_3324477 := by
    simpa [prefixWord, tailWord_3324477, baseEnd_3324477] using wordTrace_append hprefix tailTrace_3324477
  have hstable : (prefixWord ++ tailWord_3324477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324477).length < 2 ^ (prefixWord ++ tailWord_3324477).sum := by decide
  have hdescent : baseEnd_3324477 < baseStart_3324477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324494 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_3324494 : Nat := 118140960795 + 3324494 * 2 ^ 59
def prefixEnd_3324494 : Nat := 4983230072969 + 3 ^ 40 * 3324494 * 2
def baseEnd_3324494 : Nat := 1138042236658947423757291

theorem tailTrace_3324494 : CollatzResearch.WordTrace tailWord_3324494 prefixEnd_3324494 1138042236658947423757291 := by
  unfold tailWord_3324494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15156782202241686402145567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80836171745288994144776357 15156782202241686402145567)
  ·
    refine ⟨22735173303362529603218351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15156782202241686402145567 22735173303362529603218351)
    ·
      refine ⟨34102759955043794404827527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22735173303362529603218351 34102759955043794404827527)
      ·
        refine ⟨51154139932565691607241291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34102759955043794404827527 51154139932565691607241291)
        ·
          refine ⟨76731209898848537410861937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51154139932565691607241291 76731209898848537410861937)
          ·
            refine ⟨57548407424136403058146453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76731209898848537410861937 57548407424136403058146453)
            ·
              refine ⟨2697581598006393893350615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57548407424136403058146453 2697581598006393893350615)
              ·
                refine ⟨4046372397009590840025923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697581598006393893350615 4046372397009590840025923)
                ·
                  refine ⟨6069558595514386260038885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046372397009590840025923 6069558595514386260038885)
                  ·
                    refine ⟨1138042236658947423757291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6069558595514386260038885 1138042236658947423757291)
                    ·
                      rfl

theorem cell22_3324494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_3324494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324494 prefixEnd_3324494 := by exact prefixLift 3324494
  have htrace : WordTrace (prefixWord ++ tailWord_3324494) baseStart_3324494 baseEnd_3324494 := by
    simpa [prefixWord, tailWord_3324494, baseEnd_3324494] using wordTrace_append hprefix tailTrace_3324494
  have hstable : (prefixWord ++ tailWord_3324494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324494).length < 2 ^ (prefixWord ++ tailWord_3324494).sum := by decide
  have hdescent : baseEnd_3324494 < baseStart_3324494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324537 : List Nat := [1, 2, 1, 3, 3, 2, 4, 6]
def baseStart_3324537 : Nat := 118140960795 + 3324537 * 2 ^ 59
def prefixEnd_3324537 : Nat := 4983230072969 + 3 ^ 40 * 3324537 * 2
def baseEnd_3324537 : Nat := 126450772937523293881351

theorem tailTrace_3324537 : CollatzResearch.WordTrace tailWord_3324537 prefixEnd_3324537 126450772937523293881351 := by
  unfold tailWord_3324537
  simp only [CollatzResearch.WordTrace]
  refine ⟨121255825956777709560979865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80837217304518473040653243 121255825956777709560979865)
  ·
    refine ⟨90941869467583282170734899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121255825956777709560979865 90941869467583282170734899)
    ·
      refine ⟨136412804201374923256102349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90941869467583282170734899 136412804201374923256102349)
      ·
        refine ⟨51154801575515596221038381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136412804201374923256102349 51154801575515596221038381)
        ·
          refine ⟨19183050590818348582889393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51154801575515596221038381 19183050590818348582889393)
          ·
            refine ⟨14387287943113761437167045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19183050590818348582889393 14387287943113761437167045)
            ·
              refine ⟨2697616489333830269468821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14387287943113761437167045 2697616489333830269468821)
              ·
                refine ⟨126450772937523293881351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2697616489333830269468821 126450772937523293881351)
                ·
                  rfl

theorem cell22_3324537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 6].length) (baseStart_3324537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324537 prefixEnd_3324537 := by exact prefixLift 3324537
  have htrace : WordTrace (prefixWord ++ tailWord_3324537) baseStart_3324537 baseEnd_3324537 := by
    simpa [prefixWord, tailWord_3324537, baseEnd_3324537] using wordTrace_append hprefix tailTrace_3324537
  have hstable : (prefixWord ++ tailWord_3324537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324537).length < 2 ^ (prefixWord ++ tailWord_3324537).sum := by decide
  have hdescent : baseEnd_3324537 < baseStart_3324537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324554 : List Nat := [3, 1, 2, 3, 4, 1, 8]
def baseStart_3324554 : Nat := 118140960795 + 3324554 * 2 ^ 59
def prefixEnd_3324554 : Nat := 4983230072969 + 3 ^ 40 * 3324554 * 2
def baseEnd_3324554 : Nat := 42150473180930639528041

theorem tailTrace_3324554 : CollatzResearch.WordTrace tailWord_3324554 prefixEnd_3324554 42150473180930639528041 := by
  unfold tailWord_3324554
  simp only [CollatzResearch.WordTrace]
  refine ⟨30314111499429030366087179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80837630665144080976232477 30314111499429030366087179)
  ·
    refine ⟨45471167249143545549130769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30314111499429030366087179 45471167249143545549130769)
    ·
      refine ⟨34103375436857659161848077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45471167249143545549130769 34103375436857659161848077)
      ·
        refine ⟨12788765788821622185693029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34103375436857659161848077 12788765788821622185693029)
        ·
          refine ⟨2397893585404054159817443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12788765788821622185693029 2397893585404054159817443)
          ·
            refine ⟨3596840378106081239726165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2397893585404054159817443 3596840378106081239726165)
            ·
              refine ⟨42150473180930639528041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3596840378106081239726165 42150473180930639528041)
              ·
                rfl

theorem cell22_3324554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 8].length) (baseStart_3324554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324554 prefixEnd_3324554 := by exact prefixLift 3324554
  have htrace : WordTrace (prefixWord ++ tailWord_3324554) baseStart_3324554 baseEnd_3324554 := by
    simpa [prefixWord, tailWord_3324554, baseEnd_3324554] using wordTrace_append hprefix tailTrace_3324554
  have hstable : (prefixWord ++ tailWord_3324554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324554).length < 2 ^ (prefixWord ++ tailWord_3324554).sum := by decide
  have hdescent : baseEnd_3324554 < baseStart_3324554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324620 : List Nat := [2, 2, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_3324620 : Nat := 118140960795 + 3324620 * 2 ^ 59
def prefixEnd_3324620 : Nat := 4983230072969 + 3 ^ 40 * 3324620 * 2
def baseEnd_3324620 : Nat := 1138085369033925095106905

theorem tailTrace_3324620 : CollatzResearch.WordTrace tailWord_3324620 prefixEnd_3324620 1138085369033925095106905 := by
  unfold tailWord_3324620
  simp only [CollatzResearch.WordTrace]
  refine ⟨60629426607738507368125657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80839235476984676490834209 60629426607738507368125657)
  ·
    refine ⟨45472069955803880526094243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60629426607738507368125657 45472069955803880526094243)
    ·
      refine ⟨68208104933705820789141365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45472069955803880526094243 68208104933705820789141365)
      ·
        refine ⟨6394509837534920698982003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68208104933705820789141365 6394509837534920698982003)
        ·
          refine ⟨9591764756302381048473005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6394509837534920698982003 9591764756302381048473005)
          ·
            refine ⟨3596911783613392893177377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9591764756302381048473005 3596911783613392893177377)
            ·
              refine ⟨2697683837710044669883033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3596911783613392893177377 2697683837710044669883033)
              ·
                refine ⟨2023262878282533502412275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697683837710044669883033 2023262878282533502412275)
                ·
                  refine ⟨3034894317423800253618413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023262878282533502412275 3034894317423800253618413)
                  ·
                    refine ⟨1138085369033925095106905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034894317423800253618413 1138085369033925095106905)
                    ·
                      rfl

theorem cell22_3324620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_3324620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324620 prefixEnd_3324620 := by exact prefixLift 3324620
  have htrace : WordTrace (prefixWord ++ tailWord_3324620) baseStart_3324620 baseEnd_3324620 := by
    simpa [prefixWord, tailWord_3324620, baseEnd_3324620] using wordTrace_append hprefix tailTrace_3324620
  have hstable : (prefixWord ++ tailWord_3324620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324620).length < 2 ^ (prefixWord ++ tailWord_3324620).sum := by decide
  have hdescent : baseEnd_3324620 < baseStart_3324620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324657 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_3324657 : Nat := 118140960795 + 3324657 * 2 ^ 59
def prefixEnd_3324657 : Nat := 4983230072969 + 3 ^ 40 * 3324657 * 2
def baseEnd_3324657 : Nat := 1138098034890069331931791

theorem tailTrace_3324657 : CollatzResearch.WordTrace tailWord_3324657 prefixEnd_3324657 1138098034890069331931791 := by
  unfold tailWord_3324657
  simp only [CollatzResearch.WordTrace]
  refine ⟨121260202716342970055348225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80840135144228646703565483 121260202716342970055348225)
  ·
    refine ⟨90945152037257227541511169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121260202716342970055348225 90945152037257227541511169)
    ·
      refine ⟨68208864027942920656133377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90945152037257227541511169 68208864027942920656133377)
      ·
        refine ⟨51156648020957190492100033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68208864027942920656133377 51156648020957190492100033)
        ·
          refine ⟨38367486015717892869075025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51156648020957190492100033 38367486015717892869075025)
          ·
            refine ⟨28775614511788419651806269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38367486015717892869075025 28775614511788419651806269)
            ·
              refine ⟨10790855441920657369427351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28775614511788419651806269 10790855441920657369427351)
              ·
                refine ⟨16186283162880986054141027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10790855441920657369427351 16186283162880986054141027)
                ·
                  refine ⟨24279424744321479081211541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16186283162880986054141027 24279424744321479081211541)
                  ·
                    refine ⟨1138098034890069331931791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24279424744321479081211541 1138098034890069331931791)
                    ·
                      rfl

theorem cell22_3324657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_3324657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324657 prefixEnd_3324657 := by exact prefixLift 3324657
  have htrace : WordTrace (prefixWord ++ tailWord_3324657) baseStart_3324657 baseEnd_3324657 := by
    simpa [prefixWord, tailWord_3324657, baseEnd_3324657] using wordTrace_append hprefix tailTrace_3324657
  have hstable : (prefixWord ++ tailWord_3324657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324657).length < 2 ^ (prefixWord ++ tailWord_3324657).sum := by decide
  have hdescent : baseEnd_3324657 < baseStart_3324657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324706 : List Nat := [3, 3, 1, 1, 2, 4, 2, 6]
def baseStart_3324706 : Nat := 118140960795 + 3324706 * 2 ^ 59
def prefixEnd_3324706 : Nat := 4983230072969 + 3 ^ 40 * 3324706 * 2
def baseEnd_3324706 : Nat := 126457200954605504161849

theorem tailTrace_3324706 : CollatzResearch.WordTrace tailWord_3324706 prefixEnd_3324706 126457200954605504161849 := by
  unfold tailWord_3324706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30315497473291362855970493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80841326595443634282587981 30315497473291362855970493)
  ·
    refine ⟨11368311552484261070988935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30315497473291362855970493 11368311552484261070988935)
    ·
      refine ⟨17052467328726391606483403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11368311552484261070988935 17052467328726391606483403)
      ·
        refine ⟨25578700993089587409725105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17052467328726391606483403 25578700993089587409725105)
        ·
          refine ⟨19184025744817190557293829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25578700993089587409725105 19184025744817190557293829)
          ·
            refine ⟨3597004827153223229492593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19184025744817190557293829 3597004827153223229492593)
            ·
              refine ⟨2697753620364917422119445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597004827153223229492593 2697753620364917422119445)
              ·
                refine ⟨126457200954605504161849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2697753620364917422119445 126457200954605504161849)
                ·
                  rfl

theorem cell22_3324706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_3324706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324706 prefixEnd_3324706 := by exact prefixLift 3324706
  have htrace : WordTrace (prefixWord ++ tailWord_3324706) baseStart_3324706 baseEnd_3324706 := by
    simpa [prefixWord, tailWord_3324706, baseEnd_3324706] using wordTrace_append hprefix tailTrace_3324706
  have hstable : (prefixWord ++ tailWord_3324706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324706).length < 2 ^ (prefixWord ++ tailWord_3324706).sum := by decide
  have hdescent : baseEnd_3324706 < baseStart_3324706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324811 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 2, 3]
def baseStart_3324811 : Nat := 118140960795 + 3324811 * 2 ^ 59
def prefixEnd_3324811 : Nat := 4983230072969 + 3 ^ 40 * 3324811 * 2
def baseEnd_3324811 : Nat := 1138150752237264263581319

theorem tailTrace_3324811 : CollatzResearch.WordTrace tailWord_3324811 prefixEnd_3324811 1138150752237264263581319 := by
  unfold tailWord_3324811
  simp only [CollatzResearch.WordTrace]
  refine ⟨121265819557785054356454287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80843879705190036237636191 121265819557785054356454287)
  ·
    refine ⟨181898729336677581534681431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121265819557785054356454287 181898729336677581534681431)
    ·
      refine ⟨272848094005016372302022147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181898729336677581534681431 272848094005016372302022147)
      ·
        refine ⟨409272141007524558453033221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272848094005016372302022147 409272141007524558453033221)
        ·
          refine ⟨76738526438910854709943729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409272141007524558453033221 76738526438910854709943729)
          ·
            refine ⟨57553894829183141032457797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76738526438910854709943729 57553894829183141032457797)
            ·
              refine ⟨10791355280471838943585837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57553894829183141032457797 10791355280471838943585837)
              ·
                refine ⟨4046758230176939603844689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10791355280471838943585837 4046758230176939603844689)
                ·
                  refine ⟨3035068672632704702883517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4046758230176939603844689 3035068672632704702883517)
                  ·
                    refine ⟨1138150752237264263581319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035068672632704702883517 1138150752237264263581319)
                    ·
                      rfl

theorem cell22_3324811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 3].length) (baseStart_3324811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324811 prefixEnd_3324811 := by exact prefixLift 3324811
  have htrace : WordTrace (prefixWord ++ tailWord_3324811) baseStart_3324811 baseEnd_3324811 := by
    simpa [prefixWord, tailWord_3324811, baseEnd_3324811] using wordTrace_append hprefix tailTrace_3324811
  have hstable : (prefixWord ++ tailWord_3324811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324811).length < 2 ^ (prefixWord ++ tailWord_3324811).sum := by decide
  have hdescent : baseEnd_3324811 < baseStart_3324811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324826 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_3324826 : Nat := 118140960795 + 3324826 * 2 ^ 59
def prefixEnd_3324826 : Nat := 4983230072969 + 3 ^ 40 * 3324826 * 2
def baseEnd_3324826 : Nat := 1138155887043809224456273

theorem tailTrace_3324826 : CollatzResearch.WordTrace tailWord_3324826 prefixEnd_3324826 1138155887043809224456273 := by
  unfold tailWord_3324826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30316591663182677979562583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80844244435153807945500221 30316591663182677979562583)
  ·
    refine ⟨45474887494774016969343875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30316591663182677979562583 45474887494774016969343875)
    ·
      refine ⟨68212331242161025454015813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45474887494774016969343875 68212331242161025454015813)
      ·
        refine ⟨12789812107905192272627965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68212331242161025454015813 12789812107905192272627965)
        ·
          refine ⟨4796179540464447102235487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12789812107905192272627965 4796179540464447102235487)
          ·
            refine ⟨7194269310696670653353231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4796179540464447102235487 7194269310696670653353231)
            ·
              refine ⟨10791403966045005980029847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7194269310696670653353231 10791403966045005980029847)
              ·
                refine ⟨16187105949067508970044771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10791403966045005980029847 16187105949067508970044771)
                ·
                  refine ⟨24280658923601263455067157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16187105949067508970044771 24280658923601263455067157)
                  ·
                    refine ⟨1138155887043809224456273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24280658923601263455067157 1138155887043809224456273)
                    ·
                      rfl

theorem cell22_3324826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_3324826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324826 prefixEnd_3324826 := by exact prefixLift 3324826
  have htrace : WordTrace (prefixWord ++ tailWord_3324826) baseStart_3324826 baseEnd_3324826 := by
    simpa [prefixWord, tailWord_3324826, baseEnd_3324826] using wordTrace_append hprefix tailTrace_3324826
  have hstable : (prefixWord ++ tailWord_3324826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324826).length < 2 ^ (prefixWord ++ tailWord_3324826).sum := by decide
  have hdescent : baseEnd_3324826 < baseStart_3324826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324845 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3324845 : Nat := 118140960795 + 3324845 * 2 ^ 59
def prefixEnd_3324845 : Nat := 4983230072969 + 3 ^ 40 * 3324845 * 2
def baseEnd_3324845 : Nat := 1138162391132099508231215

theorem tailTrace_3324845 : CollatzResearch.WordTrace tailWord_3324845 prefixEnd_3324845 1138162391132099508231215 := by
  unfold tailWord_3324845
  simp only [CollatzResearch.WordTrace]
  refine ⟨121267059639661878163191989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80844706426441252108794659 121267059639661878163191989)
  ·
    refine ⟨11368786841218301077799249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121267059639661878163191989 11368786841218301077799249)
    ·
      refine ⟨8526590130913725808349437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11368786841218301077799249 8526590130913725808349437)
      ·
        refine ⟨3197471299092647178131039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8526590130913725808349437 3197471299092647178131039)
        ·
          refine ⟨4796206948638970767196559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197471299092647178131039 4796206948638970767196559)
          ·
            refine ⟨7194310422958456150794839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4796206948638970767196559 7194310422958456150794839)
            ·
              refine ⟨10791465634437684226192259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7194310422958456150794839 10791465634437684226192259)
              ·
                refine ⟨16187198451656526339288389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10791465634437684226192259 16187198451656526339288389)
                ·
                  refine ⟨3035099709685598688616573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16187198451656526339288389 3035099709685598688616573)
                  ·
                    refine ⟨1138162391132099508231215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035099709685598688616573 1138162391132099508231215)
                    ·
                      rfl

theorem cell22_3324845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3324845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324845 prefixEnd_3324845 := by exact prefixLift 3324845
  have htrace : WordTrace (prefixWord ++ tailWord_3324845) baseStart_3324845 baseEnd_3324845 := by
    simpa [prefixWord, tailWord_3324845, baseEnd_3324845] using wordTrace_append hprefix tailTrace_3324845
  have hstable : (prefixWord ++ tailWord_3324845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324845).length < 2 ^ (prefixWord ++ tailWord_3324845).sum := by decide
  have hdescent : baseEnd_3324845 < baseStart_3324845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324856 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 3, 3]
def baseStart_3324856 : Nat := 118140960795 + 3324856 * 2 ^ 59
def prefixEnd_3324856 : Nat := 4983230072969 + 3 ^ 40 * 3324856 * 2
def baseEnd_3324856 : Nat := 1138166156656899146206181

theorem tailTrace_3324856 : CollatzResearch.WordTrace tailWord_3324856 prefixEnd_3324856 1138166156656899146206181 := by
  unfold tailWord_3324856
  simp only [CollatzResearch.WordTrace]
  refine ⟨60633730421311013520921211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80844973895081351361228281 60633730421311013520921211)
  ·
    refine ⟨90950595631966520281381817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60633730421311013520921211 90950595631966520281381817)
    ·
      refine ⟨68212946723974890211036363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90950595631966520281381817 68212946723974890211036363)
      ·
        refine ⟨102319420085962335316554545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68212946723974890211036363 102319420085962335316554545)
        ·
          refine ⟨76739565064471751487415909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102319420085962335316554545 76739565064471751487415909)
          ·
            refine ⟨14388668449588453403890483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76739565064471751487415909 14388668449588453403890483)
            ·
              refine ⟨21583002674382680105835725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14388668449588453403890483 21583002674382680105835725)
              ·
                refine ⟨8093626002893505039688397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21583002674382680105835725 8093626002893505039688397)
                ·
                  refine ⟨3035109751085064389883149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8093626002893505039688397 3035109751085064389883149)
                  ·
                    refine ⟨1138166156656899146206181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035109751085064389883149 1138166156656899146206181)
                    ·
                      rfl

theorem cell22_3324856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_3324856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324856 prefixEnd_3324856 := by exact prefixLift 3324856
  have htrace : WordTrace (prefixWord ++ tailWord_3324856) baseStart_3324856 baseEnd_3324856 := by
    simpa [prefixWord, tailWord_3324856, baseEnd_3324856] using wordTrace_append hprefix tailTrace_3324856
  have hstable : (prefixWord ++ tailWord_3324856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324856).length < 2 ^ (prefixWord ++ tailWord_3324856).sum := by decide
  have hdescent : baseEnd_3324856 < baseStart_3324856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324890 : List Nat := [3, 1, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_3324890 : Nat := 118140960795 + 3324890 * 2 ^ 59
def prefixEnd_3324890 : Nat := 4983230072969 + 3 ^ 40 * 3324890 * 2
def baseEnd_3324890 : Nat := 1138177795551734390856077

theorem tailTrace_3324890 : CollatzResearch.WordTrace tailWord_3324890 prefixEnd_3324890 1138177795551734390856077 := by
  unfold tailWord_3324890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30317175231124712712145031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80845800616332567232386749 30317175231124712712145031)
  ·
    refine ⟨45475762846687069068217547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30317175231124712712145031 45475762846687069068217547)
    ·
      refine ⟨68213644270030603602326321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45475762846687069068217547 68213644270030603602326321)
      ·
        refine ⟨51160233202522952701744741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68213644270030603602326321 51160233202522952701744741)
        ·
          refine ⟨9592543725473053631577139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51160233202522952701744741 9592543725473053631577139)
          ·
            refine ⟨14388815588209580447365709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9592543725473053631577139 14388815588209580447365709)
            ·
              refine ⟨5395805845578592667762141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14388815588209580447365709 5395805845578592667762141)
              ·
                refine ⟨2023427192091972250410803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5395805845578592667762141 2023427192091972250410803)
                ·
                  refine ⟨3035140788137958375616205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023427192091972250410803 3035140788137958375616205)
                  ·
                    refine ⟨1138177795551734390856077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035140788137958375616205 1138177795551734390856077)
                    ·
                      rfl

theorem cell22_3324890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_3324890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324890 prefixEnd_3324890 := by exact prefixLift 3324890
  have htrace : WordTrace (prefixWord ++ tailWord_3324890) baseStart_3324890 baseEnd_3324890 := by
    simpa [prefixWord, tailWord_3324890, baseEnd_3324890] using wordTrace_append hprefix tailTrace_3324890
  have hstable : (prefixWord ++ tailWord_3324890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324890).length < 2 ^ (prefixWord ++ tailWord_3324890).sum := by decide
  have hdescent : baseEnd_3324890 < baseStart_3324890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324959 : List Nat := [1, 1, 2, 4, 1, 13]
def baseStart_3324959 : Nat := 118140960795 + 3324959 * 2 ^ 59
def prefixEnd_3324959 : Nat := 4983230072969 + 3 ^ 40 * 3324959 * 2
def baseEnd_3324959 : Nat := 14051869329158533467665

theorem tailTrace_3324959 : CollatzResearch.WordTrace tailWord_3324959 prefixEnd_3324959 14051869329158533467665 := by
  unfold tailWord_3324959
  simp only [CollatzResearch.WordTrace]
  refine ⟨121271217561248875632841931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80847478374165917088561287 121271217561248875632841931)
  ·
    refine ⟨181906826341873313449262897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121271217561248875632841931 181906826341873313449262897)
    ·
      refine ⟨136430119756404985086947173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181906826341873313449262897 136430119756404985086947173)
      ·
        refine ⟨25580647454325934703802595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136430119756404985086947173 25580647454325934703802595)
        ·
          refine ⟨38370971181488902055703893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25580647454325934703802595 38370971181488902055703893)
          ·
            refine ⟨14051869329158533467665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38370971181488902055703893 14051869329158533467665)
            ·
              rfl

theorem cell22_3324959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 13].length) (baseStart_3324959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324959 prefixEnd_3324959 := by exact prefixLift 3324959
  have htrace : WordTrace (prefixWord ++ tailWord_3324959) baseStart_3324959 baseEnd_3324959 := by
    simpa [prefixWord, tailWord_3324959, baseEnd_3324959] using wordTrace_append hprefix tailTrace_3324959
  have hstable : (prefixWord ++ tailWord_3324959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324959).length < 2 ^ (prefixWord ++ tailWord_3324959).sum := by decide
  have hdescent : baseEnd_3324959 < baseStart_3324959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324963 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 2, 3]
def baseStart_3324963 : Nat := 118140960795 + 3324963 * 2 ^ 59
def prefixEnd_3324963 : Nat := 4983230072969 + 3 ^ 40 * 3324963 * 2
def baseEnd_3324963 : Nat := 1138202784943586533780853

theorem tailTrace_3324963 : CollatzResearch.WordTrace tailWord_3324963 prefixEnd_3324963 1138202784943586533780853 := by
  unfold tailWord_3324963
  simp only [CollatzResearch.WordTrace]
  refine ⟨121271363453234384315987543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80847575635489589543991695 121271363453234384315987543)
  ·
    refine ⟨181907045179851576473981315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121271363453234384315987543 181907045179851576473981315)
    ·
      refine ⟨272860567769777364710971973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181907045179851576473981315 272860567769777364710971973)
      ·
        refine ⟨51161356456833255883307245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272860567769777364710971973 51161356456833255883307245)
        ·
          refine ⟨19185508671312470956240217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51161356456833255883307245 19185508671312470956240217)
          ·
            refine ⟨14389131503484353217180163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19185508671312470956240217 14389131503484353217180163)
            ·
              refine ⟨21583697255226529825770245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14389131503484353217180163 21583697255226529825770245)
              ·
                refine ⟨4046943235354974342331921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21583697255226529825770245 4046943235354974342331921)
                ·
                  refine ⟨3035207426516230756748941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4046943235354974342331921 3035207426516230756748941)
                  ·
                    refine ⟨1138202784943586533780853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035207426516230756748941 1138202784943586533780853)
                    ·
                      rfl

theorem cell22_3324963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 3].length) (baseStart_3324963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324963 prefixEnd_3324963 := by exact prefixLift 3324963
  have htrace : WordTrace (prefixWord ++ tailWord_3324963) baseStart_3324963 baseEnd_3324963 := by
    simpa [prefixWord, tailWord_3324963, baseEnd_3324963] using wordTrace_append hprefix tailTrace_3324963
  have hstable : (prefixWord ++ tailWord_3324963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324963).length < 2 ^ (prefixWord ++ tailWord_3324963).sum := by decide
  have hdescent : baseEnd_3324963 < baseStart_3324963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324980 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3324980 : Nat := 118140960795 + 3324980 * 2 ^ 59
def prefixEnd_3324980 : Nat := 4983230072969 + 3 ^ 40 * 3324980 * 2
def baseEnd_3324980 : Nat := 1138208604391004156105801

theorem tailTrace_3324980 : CollatzResearch.WordTrace tailWord_3324980 prefixEnd_3324980 1138208604391004156105801 := by
  unfold tailWord_3324980
  simp only [CollatzResearch.WordTrace]
  refine ⟨60635991747086398109678197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80847988996115197479570929 60635991747086398109678197)
  ·
    refine ⟨5684624226289349822782331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60635991747086398109678197 5684624226289349822782331)
    ·
      refine ⟨8526936339434024734173497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684624226289349822782331 8526936339434024734173497)
      ·
        refine ⟨6395202254575518550630123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8526936339434024734173497 6395202254575518550630123)
        ·
          refine ⟨9592803381863277825945185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395202254575518550630123 9592803381863277825945185)
          ·
            refine ⟨7194602536397458369458889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9592803381863277825945185 7194602536397458369458889)
            ·
              refine ⟨5395951902298093777094167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7194602536397458369458889 5395951902298093777094167)
              ·
                refine ⟨8093927853447140665641251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395951902298093777094167 8093927853447140665641251)
                ·
                  refine ⟨12140891780170710998461877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8093927853447140665641251 12140891780170710998461877)
                  ·
                    refine ⟨1138208604391004156105801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12140891780170710998461877 1138208604391004156105801)
                    ·
                      rfl

theorem cell22_3324980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3324980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3324980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3324980 prefixEnd_3324980 := by exact prefixLift 3324980
  have htrace : WordTrace (prefixWord ++ tailWord_3324980) baseStart_3324980 baseEnd_3324980 := by
    simpa [prefixWord, tailWord_3324980, baseEnd_3324980] using wordTrace_append hprefix tailTrace_3324980
  have hstable : (prefixWord ++ tailWord_3324980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324980).length < 2 ^ (prefixWord ++ tailWord_3324980).sum := by decide
  have hdescent : baseEnd_3324980 < baseStart_3324980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325025 : List Nat := [1, 2, 3, 1, 1, 2, 4, 4, 1, 3]
def baseStart_3325025 : Nat := 118140960795 + 3325025 * 2 ^ 59
def prefixEnd_3325025 : Nat := 4983230072969 + 3 ^ 40 * 3325025 * 2
def baseEnd_3325025 : Nat := 1138224008810639038730663

theorem tailTrace_3325025 : CollatzResearch.WordTrace tailWord_3325025 prefixEnd_3325025 1138224008810639038730663 := by
  unfold tailWord_3325025
  simp only [CollatzResearch.WordTrace]
  refine ⟨121273624779009768904744529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80849083186006512603163019 121273624779009768904744529)
  ·
    refine ⟨90955218584257326678558397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121273624779009768904744529 90955218584257326678558397)
    ·
      refine ⟨34108206969096497504459399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90955218584257326678558397 34108206969096497504459399)
      ·
        refine ⟨51162310453644746256689099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34108206969096497504459399 51162310453644746256689099)
        ·
          refine ⟨76743465680467119385033649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51162310453644746256689099 76743465680467119385033649)
          ·
            refine ⟨57557599260350339538775237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76743465680467119385033649 57557599260350339538775237)
            ·
              refine ⟨10792049861315688663520357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57557599260350339538775237 10792049861315688663520357)
              ·
                refine ⟨2023509348996691624410067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10792049861315688663520357 2023509348996691624410067)
                ·
                  refine ⟨3035264023495037436615101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023509348996691624410067 3035264023495037436615101)
                  ·
                    refine ⟨1138224008810639038730663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035264023495037436615101 1138224008810639038730663)
                    ·
                      rfl

theorem cell22_3325025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_3325025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325025 prefixEnd_3325025 := by exact prefixLift 3325025
  have htrace : WordTrace (prefixWord ++ tailWord_3325025) baseStart_3325025 baseEnd_3325025 := by
    simpa [prefixWord, tailWord_3325025, baseEnd_3325025] using wordTrace_append hprefix tailTrace_3325025
  have hstable : (prefixWord ++ tailWord_3325025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325025).length < 2 ^ (prefixWord ++ tailWord_3325025).sum := by decide
  have hdescent : baseEnd_3325025 < baseStart_3325025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325036 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_3325036 : Nat := 118140960795 + 3325036 * 2 ^ 59
def prefixEnd_3325036 : Nat := 4983230072969 + 3 ^ 40 * 3325036 * 2
def baseEnd_3325036 : Nat := 1138227774335438676705629

theorem tailTrace_3325036 : CollatzResearch.WordTrace tailWord_3325036 prefixEnd_3325036 1138227774335438676705629 := by
  unfold tailWord_3325036
  simp only [CollatzResearch.WordTrace]
  refine ⟨60637012990984958891697481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80849350654646611855596641 60637012990984958891697481)
  ·
    refine ⟨45477759743238719168773111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60637012990984958891697481 45477759743238719168773111)
    ·
      refine ⟨68216639614858078753159667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45477759743238719168773111 68216639614858078753159667)
      ·
        refine ⟨102324959422287118129739501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68216639614858078753159667 102324959422287118129739501)
        ·
          refine ⟨38371859783357669298652313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102324959422287118129739501 38371859783357669298652313)
          ·
            refine ⟨28778894837518251973989235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38371859783357669298652313 28778894837518251973989235)
            ·
              refine ⟨43168342256277377960983853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28778894837518251973989235 43168342256277377960983853)
              ·
                refine ⟨16188128346104016735368945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43168342256277377960983853 16188128346104016735368945)
                ·
                  refine ⟨12141096259578012551526709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16188128346104016735368945 12141096259578012551526709)
                  ·
                    refine ⟨1138227774335438676705629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12141096259578012551526709 1138227774335438676705629)
                    ·
                      rfl

theorem cell22_3325036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_3325036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325036 prefixEnd_3325036 := by exact prefixLift 3325036
  have htrace : WordTrace (prefixWord ++ tailWord_3325036) baseStart_3325036 baseEnd_3325036 := by
    simpa [prefixWord, tailWord_3325036, baseEnd_3325036] using wordTrace_append hprefix tailTrace_3325036
  have hstable : (prefixWord ++ tailWord_3325036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325036).length < 2 ^ (prefixWord ++ tailWord_3325036).sum := by decide
  have hdescent : baseEnd_3325036 < baseStart_3325036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325051 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 3, 4]
def baseStart_3325051 : Nat := 118140960795 + 3325051 * 2 ^ 59
def prefixEnd_3325051 : Nat := 4983230072969 + 3 ^ 40 * 3325051 * 2
def baseEnd_3325051 : Nat := 1138232909141983637580583

theorem tailTrace_3325051 : CollatzResearch.WordTrace tailWord_3325051 prefixEnd_3325051 1138232909141983637580583 := by
  unfold tailWord_3325051
  simp only [CollatzResearch.WordTrace]
  refine ⟨121274573076915575345191007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80849715384610383563460671 121274573076915575345191007)
  ·
    refine ⟨181911859615373363017786511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121274573076915575345191007 181911859615373363017786511)
    ·
      refine ⟨272867789423060044526679767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181911859615373363017786511 272867789423060044526679767)
      ·
        refine ⟨409301684134590066790019651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272867789423060044526679767 409301684134590066790019651)
        ·
          refine ⟨613952526201885100185029477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409301684134590066790019651 613952526201885100185029477)
          ·
            refine ⟨115116098662853456284693027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 613952526201885100185029477 115116098662853456284693027)
            ·
              refine ⟨172674147994280184427039541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115116098662853456284693027 172674147994280184427039541)
              ·
                refine ⟨16188201374463767290034957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172674147994280184427039541 16188201374463767290034957)
                ·
                  refine ⟨6070575515423912733763109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16188201374463767290034957 6070575515423912733763109)
                  ·
                    refine ⟨1138232909141983637580583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6070575515423912733763109 1138232909141983637580583)
                    ·
                      rfl

theorem cell22_3325051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_3325051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325051 prefixEnd_3325051 := by exact prefixLift 3325051
  have htrace : WordTrace (prefixWord ++ tailWord_3325051) baseStart_3325051 baseEnd_3325051 := by
    simpa [prefixWord, tailWord_3325051, baseEnd_3325051] using wordTrace_append hprefix tailTrace_3325051
  have hstable : (prefixWord ++ tailWord_3325051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325051).length < 2 ^ (prefixWord ++ tailWord_3325051).sum := by decide
  have hdescent : baseEnd_3325051 < baseStart_3325051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325111 : List Nat := [1, 1, 3, 1, 4, 1, 1, 10]
def baseStart_3325111 : Nat := 118140960795 + 3325111 * 2 ^ 59
def prefixEnd_3325111 : Nat := 4983230072969 + 3 ^ 40 * 3325111 * 2
def baseEnd_3325111 : Nat := 126472605374240386786711

theorem tailTrace_3325111 : CollatzResearch.WordTrace tailWord_3325111 prefixEnd_3325111 126472605374240386786711 := by
  unfold tailWord_3325111
  simp only [CollatzResearch.WordTrace]
  refine ⟨121276761456698205592375187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80851174304465470394916791 121276761456698205592375187)
  ·
    refine ⟨181915142185047308388562781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121276761456698205592375187 181915142185047308388562781)
    ·
      refine ⟨68218178319392740645711043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181915142185047308388562781 68218178319392740645711043)
      ·
        refine ⟨102327267479089110968566565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68218178319392740645711043 102327267479089110968566565)
        ·
          refine ⟨19186362652329208306606231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102327267479089110968566565 19186362652329208306606231)
          ·
            refine ⟨28779543978493812459909347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19186362652329208306606231 28779543978493812459909347)
            ·
              refine ⟨43169315967740718689864021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28779543978493812459909347 43169315967740718689864021)
              ·
                refine ⟨126472605374240386786711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43169315967740718689864021 126472605374240386786711)
                ·
                  rfl

theorem cell22_3325111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 10].length) (baseStart_3325111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325111 prefixEnd_3325111 := by exact prefixLift 3325111
  have htrace : WordTrace (prefixWord ++ tailWord_3325111) baseStart_3325111 baseEnd_3325111 := by
    simpa [prefixWord, tailWord_3325111, baseEnd_3325111] using wordTrace_append hprefix tailTrace_3325111
  have hstable : (prefixWord ++ tailWord_3325111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325111).length < 2 ^ (prefixWord ++ tailWord_3325111).sum := by decide
  have hdescent : baseEnd_3325111 < baseStart_3325111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325113 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_3325113 : Nat := 118140960795 + 3325113 * 2 ^ 59
def prefixEnd_3325113 : Nat := 4983230072969 + 3 ^ 40 * 3325113 * 2
def baseEnd_3325113 : Nat := 1138254133009036142530393

theorem tailTrace_3325113 : CollatzResearch.WordTrace tailWord_3325113 prefixEnd_3325113 1138254133009036142530393 := by
  unfold tailWord_3325113
  simp only [CollatzResearch.WordTrace]
  refine ⟨121276834402690959933947993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80851222935127306622631995 121276834402690959933947993)
  ·
    refine ⟨90957625802018219950460995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121276834402690959933947993 90957625802018219950460995)
    ·
      refine ⟨136436438703027329925691493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90957625802018219950460995 136436438703027329925691493)
      ·
        refine ⟨25581832256817624361067155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136436438703027329925691493 25581832256817624361067155)
        ·
          refine ⟨38372748385226436541600733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25581832256817624361067155 38372748385226436541600733)
          ·
            refine ⟨14389780644459913703100275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38372748385226436541600733 14389780644459913703100275)
            ·
              refine ⟨21584670966689870554650413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14389780644459913703100275 21584670966689870554650413)
              ·
                refine ⟨8094251612508701457993905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21584670966689870554650413 8094251612508701457993905)
                ·
                  refine ⟨6070688709381526093495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8094251612508701457993905 6070688709381526093495429)
                  ·
                    refine ⟨1138254133009036142530393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6070688709381526093495429 1138254133009036142530393)
                    ·
                      rfl

theorem cell22_3325113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_3325113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325113 prefixEnd_3325113 := by exact prefixLift 3325113
  have htrace : WordTrace (prefixWord ++ tailWord_3325113) baseStart_3325113 baseEnd_3325113 := by
    simpa [prefixWord, tailWord_3325113, baseEnd_3325113] using wordTrace_append hprefix tailTrace_3325113
  have hstable : (prefixWord ++ tailWord_3325113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325113).length < 2 ^ (prefixWord ++ tailWord_3325113).sum := by decide
  have hdescent : baseEnd_3325113 < baseStart_3325113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325134 : List Nat := [4, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_3325134 : Nat := 118140960795 + 3325134 * 2 ^ 59
def prefixEnd_3325134 : Nat := 4983230072969 + 3 ^ 40 * 3325134 * 2
def baseEnd_3325134 : Nat := 379420440579399695918443

theorem tailTrace_3325134 : CollatzResearch.WordTrace tailWord_3325134 prefixEnd_3325134 379420440579399695918443 := by
  unfold tailWord_3325134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15159700041951860065057807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80851733557076587013641637 15159700041951860065057807)
  ·
    refine ⟨22739550062927790097586711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15159700041951860065057807 22739550062927790097586711)
    ·
      refine ⟨34109325094391685146380067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22739550062927790097586711 34109325094391685146380067)
      ·
        refine ⟨51163987641587527719570101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34109325094391685146380067 51163987641587527719570101)
        ·
          refine ⟨4796623841398830723709697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51163987641587527719570101 4796623841398830723709697)
          ·
            refine ⟨3597467881049123042782273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4796623841398830723709697 3597467881049123042782273)
            ·
              refine ⟨2698100910786842282086705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597467881049123042782273 2698100910786842282086705)
              ·
                refine ⟨2023575683090131711565029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698100910786842282086705 2023575683090131711565029)
                ·
                  refine ⟨379420440579399695918443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023575683090131711565029 379420440579399695918443)
                  ·
                    rfl

theorem cell22_3325134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_3325134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325134 prefixEnd_3325134 := by exact prefixLift 3325134
  have htrace : WordTrace (prefixWord ++ tailWord_3325134) baseStart_3325134 baseEnd_3325134 := by
    simpa [prefixWord, tailWord_3325134, baseEnd_3325134] using wordTrace_append hprefix tailTrace_3325134
  have hstable : (prefixWord ++ tailWord_3325134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325134).length < 2 ^ (prefixWord ++ tailWord_3325134).sum := by decide
  have hdescent : baseEnd_3325134 < baseStart_3325134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325160 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 3, 3]
def baseStart_3325160 : Nat := 118140960795 + 3325160 * 2 ^ 59
def prefixEnd_3325160 : Nat := 4983230072969 + 3 ^ 40 * 3325160 * 2
def baseEnd_3325160 : Nat := 1138270222069543686605249

theorem tailTrace_3325160 : CollatzResearch.WordTrace tailWord_3325160 prefixEnd_3325160 1138270222069543686605249 := by
  unfold tailWord_3325160
  simp only [CollatzResearch.WordTrace]
  refine ⟨60639274316760343480454467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80852365755680457973939289 60639274316760343480454467)
  ·
    refine ⟨90958911475140515220681701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60639274316760343480454467 90958911475140515220681701)
    ·
      refine ⟨17054795901588846603877819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90958911475140515220681701 17054795901588846603877819)
      ·
        refine ⟨25582193852383269905816729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17054795901588846603877819 25582193852383269905816729)
        ·
          refine ⟨19186645389287452429362547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25582193852383269905816729 19186645389287452429362547)
          ·
            refine ⟨28779968083931178644043821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19186645389287452429362547 28779968083931178644043821)
            ·
              refine ⟨10792488031474191991516433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28779968083931178644043821 10792488031474191991516433)
              ·
                refine ⟨8094366023605643993637325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10792488031474191991516433 8094366023605643993637325)
                ·
                  refine ⟨3035387258852116497613997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8094366023605643993637325 3035387258852116497613997)
                  ·
                    refine ⟨1138270222069543686605249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035387258852116497613997 1138270222069543686605249)
                    ·
                      rfl

theorem cell22_3325160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_3325160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325160 prefixEnd_3325160 := by exact prefixLift 3325160
  have htrace : WordTrace (prefixWord ++ tailWord_3325160) baseStart_3325160 baseEnd_3325160 := by
    simpa [prefixWord, tailWord_3325160, baseEnd_3325160] using wordTrace_append hprefix tailTrace_3325160
  have hstable : (prefixWord ++ tailWord_3325160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325160).length < 2 ^ (prefixWord ++ tailWord_3325160).sum := by decide
  have hdescent : baseEnd_3325160 < baseStart_3325160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325177 : List Nat := [1, 2, 1, 3, 1, 1, 6, 3, 1, 3]
def baseStart_3325177 : Nat := 118140960795 + 3325177 * 2 ^ 59
def prefixEnd_3325177 : Nat := 4983230072969 + 3 ^ 40 * 3325177 * 2
def baseEnd_3325177 : Nat := 1138276041516961308930197

theorem tailTrace_3325177 : CollatzResearch.WordTrace tailWord_3325177 prefixEnd_3325177 1138276041516961308930197 := by
  unfold tailWord_3325177
  simp only [CollatzResearch.WordTrace]
  refine ⟨121279168674459098864277785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80852779116306065909518523 121279168674459098864277785)
  ·
    refine ⟨90959376505844324148208339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121279168674459098864277785 90959376505844324148208339)
    ·
      refine ⟨136439064758766486222312509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90959376505844324148208339 136439064758766486222312509)
      ·
        refine ⟨51164649284537432333367191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136439064758766486222312509 51164649284537432333367191)
        ·
          refine ⟨76746973926806148500050787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51164649284537432333367191 76746973926806148500050787)
          ·
            refine ⟨115120460890209222750076181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76746973926806148500050787 115120460890209222750076181)
            ·
              refine ⟨5396271604228557316409821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115120460890209222750076181 5396271604228557316409821)
              ·
                refine ⟨2023601851585708993653683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5396271604228557316409821 2023601851585708993653683)
                ·
                  refine ⟨3035402777378563490480525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023601851585708993653683 3035402777378563490480525)
                  ·
                    refine ⟨1138276041516961308930197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035402777378563490480525 1138276041516961308930197)
                    ·
                      rfl

theorem cell22_3325177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 3].length) (baseStart_3325177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325177 prefixEnd_3325177 := by exact prefixLift 3325177
  have htrace : WordTrace (prefixWord ++ tailWord_3325177) baseStart_3325177 baseEnd_3325177 := by
    simpa [prefixWord, tailWord_3325177, baseEnd_3325177] using wordTrace_append hprefix tailTrace_3325177
  have hstable : (prefixWord ++ tailWord_3325177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325177).length < 2 ^ (prefixWord ++ tailWord_3325177).sum := by decide
  have hdescent : baseEnd_3325177 < baseStart_3325177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325252 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3325252 : Nat := 118140960795 + 3325252 * 2 ^ 59
def prefixEnd_3325252 : Nat := 4983230072969 + 3 ^ 40 * 3325252 * 2
def baseEnd_3325252 : Nat := 379433905183228704434989

theorem tailTrace_3325252 : CollatzResearch.WordTrace tailWord_3325252 prefixEnd_3325252 379433905183228704434989 := by
  unfold tailWord_3325252
  simp only [CollatzResearch.WordTrace]
  refine ⟨60640952074593693336629005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80854602766124924448838673 60640952074593693336629005)
  ·
    refine ⟨22740357027972635001235877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60640952074593693336629005 22740357027972635001235877)
    ·
      refine ⟨4263816942744869062731727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22740357027972635001235877 4263816942744869062731727)
      ·
        refine ⟨6395725414117303594097591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4263816942744869062731727 6395725414117303594097591)
        ·
          refine ⟨9593588121175955391146387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395725414117303594097591 9593588121175955391146387)
          ·
            refine ⟨14390382181763933086719581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9593588121175955391146387 14390382181763933086719581)
            ·
              refine ⟨5396393318161474907519843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14390382181763933086719581 5396393318161474907519843)
              ·
                refine ⟨8094589977242212361279765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5396393318161474907519843 8094589977242212361279765)
                ·
                  refine ⟨379433905183228704434989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8094589977242212361279765 379433905183228704434989)
                  ·
                    rfl

theorem cell22_3325252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3325252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325252 prefixEnd_3325252 := by exact prefixLift 3325252
  have htrace : WordTrace (prefixWord ++ tailWord_3325252) baseStart_3325252 baseEnd_3325252 := by
    simpa [prefixWord, tailWord_3325252, baseEnd_3325252] using wordTrace_append hprefix tailTrace_3325252
  have hstable : (prefixWord ++ tailWord_3325252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325252).length < 2 ^ (prefixWord ++ tailWord_3325252).sum := by decide
  have hdescent : baseEnd_3325252 < baseStart_3325252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325282 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3325282 : Nat := 118140960795 + 3325282 * 2 ^ 59
def prefixEnd_3325282 : Nat := 4983230072969 + 3 ^ 40 * 3325282 * 2
def baseEnd_3325282 : Nat := 1138311985162776035054875

theorem tailTrace_3325282 : CollatzResearch.WordTrace tailWord_3325282 prefixEnd_3325282 1138311985162776035054875 := by
  unfold tailWord_3325282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30320749584769675449212525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80855332226052467864566733 30320749584769675449212525)
  ·
    refine ⟨11370281094288628293454697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30320749584769675449212525 11370281094288628293454697)
    ·
      refine ⟨8527710820716471220091023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11370281094288628293454697 8527710820716471220091023)
      ·
        refine ⟨12791566231074706830136535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527710820716471220091023 12791566231074706830136535)
        ·
          refine ⟨19187349346612060245204803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12791566231074706830136535 19187349346612060245204803)
          ·
            refine ⟨28781024019918090367807205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19187349346612060245204803 28781024019918090367807205)
            ·
              refine ⟨5396442003734641943963851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28781024019918090367807205 5396442003734641943963851)
              ·
                refine ⟨8094663005601962915945777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5396442003734641943963851 8094663005601962915945777)
                ·
                  refine ⟨6070997254201472186959333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8094663005601962915945777 6070997254201472186959333)
                  ·
                    refine ⟨1138311985162776035054875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6070997254201472186959333 1138311985162776035054875)
                    ·
                      rfl

theorem cell22_3325282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3325282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325282 prefixEnd_3325282 := by exact prefixLift 3325282
  have htrace : WordTrace (prefixWord ++ tailWord_3325282) baseStart_3325282 baseEnd_3325282 := by
    simpa [prefixWord, tailWord_3325282, baseEnd_3325282] using wordTrace_append hprefix tailTrace_3325282
  have hstable : (prefixWord ++ tailWord_3325282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325282).length < 2 ^ (prefixWord ++ tailWord_3325282).sum := by decide
  have hdescent : baseEnd_3325282 < baseStart_3325282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325314 : List Nat := [3, 4, 2, 1, 1, 3, 1, 7]
def baseStart_3325314 : Nat := 118140960795 + 3325314 * 2 ^ 59
def prefixEnd_3325314 : Nat := 4983230072969 + 3 ^ 40 * 3325314 * 2
def baseEnd_3325314 : Nat := 126480326601859846472753

theorem tailTrace_3325314 : CollatzResearch.WordTrace tailWord_3325314 prefixEnd_3325314 126480326601859846472753 := by
  unfold tailWord_3325314
  simp only [CollatzResearch.WordTrace]
  refine ⟨30321041368740692815503749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80856110316641847508009997 30321041368740692815503749)
  ·
    refine ⟨5685195256638879902906953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30321041368740692815503749 5685195256638879902906953)
    ·
      refine ⟨4263896442479159927180215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5685195256638879902906953 4263896442479159927180215)
      ·
        refine ⟨6395844663718739890770323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4263896442479159927180215 6395844663718739890770323)
        ·
          refine ⟨9593766995578109836155485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395844663718739890770323 9593766995578109836155485)
          ·
            refine ⟨3597662623341791188558307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9593766995578109836155485 3597662623341791188558307)
            ·
              refine ⟨5396493935012686782837461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597662623341791188558307 5396493935012686782837461)
              ·
                refine ⟨126480326601859846472753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5396493935012686782837461 126480326601859846472753)
                ·
                  rfl

theorem cell22_3325314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_3325314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325314 prefixEnd_3325314 := by exact prefixLift 3325314
  have htrace : WordTrace (prefixWord ++ tailWord_3325314) baseStart_3325314 baseEnd_3325314 := by
    simpa [prefixWord, tailWord_3325314, baseEnd_3325314] using wordTrace_append hprefix tailTrace_3325314
  have hstable : (prefixWord ++ tailWord_3325314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325314).length < 2 ^ (prefixWord ++ tailWord_3325314).sum := by decide
  have hdescent : baseEnd_3325314 < baseStart_3325314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325346 : List Nat := [3, 3, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3325346 : Nat := 118140960795 + 3325346 * 2 ^ 59
def prefixEnd_3325346 : Nat := 4983230072969 + 3 ^ 40 * 3325346 * 2
def baseEnd_3325346 : Nat := 1138333893670701201454679

theorem tailTrace_3325346 : CollatzResearch.WordTrace tailWord_3325346 prefixEnd_3325346 1138333893670701201454679 := by
  unfold tailWord_3325346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30321333152711710181794973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80856888407231227151453261 30321333152711710181794973)
  ·
    refine ⟨11370499932266891318173115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30321333152711710181794973 11370499932266891318173115)
    ·
      refine ⟨17055749898400336977259673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11370499932266891318173115 17055749898400336977259673)
      ·
        refine ⟨12791812423800252732944755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17055749898400336977259673 12791812423800252732944755)
        ·
          refine ⟨19187718635700379099417133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12791812423800252732944755 19187718635700379099417133)
          ·
            refine ⟨7195394488387642162281425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19187718635700379099417133 7195394488387642162281425)
            ·
              refine ⟨5396545866290731621711069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7195394488387642162281425 5396545866290731621711069)
              ·
                refine ⟨2023704699859024358141651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5396545866290731621711069 2023704699859024358141651)
                ·
                  refine ⟨3035557049788536537212477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023704699859024358141651 3035557049788536537212477)
                  ·
                    refine ⟨1138333893670701201454679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035557049788536537212477 1138333893670701201454679)
                    ·
                      rfl

theorem cell22_3325346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3325346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325346 prefixEnd_3325346 := by exact prefixLift 3325346
  have htrace : WordTrace (prefixWord ++ tailWord_3325346) baseStart_3325346 baseEnd_3325346 := by
    simpa [prefixWord, tailWord_3325346, baseEnd_3325346] using wordTrace_append hprefix tailTrace_3325346
  have hstable : (prefixWord ++ tailWord_3325346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325346).length < 2 ^ (prefixWord ++ tailWord_3325346).sum := by decide
  have hdescent : baseEnd_3325346 < baseStart_3325346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325357 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3325357 : Nat := 118140960795 + 3325357 * 2 ^ 59
def prefixEnd_3325357 : Nat := 4983230072969 + 3 ^ 40 * 3325357 * 2
def baseEnd_3325357 : Nat := 1138337659195500839429645

theorem tailTrace_3325357 : CollatzResearch.WordTrace tailWord_3325357 prefixEnd_3325357 1138337659195500839429645 := by
  unfold tailWord_3325357
  simp only [CollatzResearch.WordTrace]
  refine ⟨121285733813806989605830325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80857155875871326403886883 121285733813806989605830325)
  ·
    refine ⟨11370537545044405275546593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121285733813806989605830325 11370537545044405275546593)
    ·
      refine ⟨8527903158783303956659945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11370537545044405275546593 8527903158783303956659945)
      ·
        refine ⟨6395927369087477967494959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8527903158783303956659945 6395927369087477967494959)
        ·
          refine ⟨9593891053631216951242439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395927369087477967494959 9593891053631216951242439)
          ·
            refine ⟨14390836580446825426863659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9593891053631216951242439 14390836580446825426863659)
            ·
              refine ⟨21586254870670238140295489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14390836580446825426863659 21586254870670238140295489)
              ·
                refine ⟨16189691153002678605221617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21586254870670238140295489 16189691153002678605221617)
                ·
                  refine ⟨12142268364752008953916213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16189691153002678605221617 12142268364752008953916213)
                  ·
                    refine ⟨1138337659195500839429645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12142268364752008953916213 1138337659195500839429645)
                    ·
                      rfl

theorem cell22_3325357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3325357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325357 prefixEnd_3325357 := by exact prefixLift 3325357
  have htrace : WordTrace (prefixWord ++ tailWord_3325357) baseStart_3325357 baseEnd_3325357 := by
    simpa [prefixWord, tailWord_3325357, baseEnd_3325357] using wordTrace_append hprefix tailTrace_3325357
  have hstable : (prefixWord ++ tailWord_3325357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325357).length < 2 ^ (prefixWord ++ tailWord_3325357).sum := by decide
  have hdescent : baseEnd_3325357 < baseStart_3325357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325400 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_3325400 : Nat := 118140960795 + 3325400 * 2 ^ 59
def prefixEnd_3325400 : Nat := 4983230072969 + 3 ^ 40 * 3325400 * 2
def baseEnd_3325400 : Nat := 1138352378974263060604513

theorem tailTrace_3325400 : CollatzResearch.WordTrace tailWord_3325400 prefixEnd_3325400 1138352378974263060604513 := by
  unfold tailWord_3325400
  simp only [CollatzResearch.WordTrace]
  refine ⟨60643651076325603974822827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80858201435100805299763769 60643651076325603974822827)
  ·
    refine ⟨90965476614488405962234241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60643651076325603974822827 90965476614488405962234241)
    ·
      refine ⟨68224107460866304471675681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90965476614488405962234241 68224107460866304471675681)
      ·
        refine ⟨51168080595649728353756761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68224107460866304471675681 51168080595649728353756761)
        ·
          refine ⟨38376060446737296265317571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51168080595649728353756761 38376060446737296265317571)
          ·
            refine ⟨57564090670105944397976357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38376060446737296265317571 57564090670105944397976357)
            ·
              refine ⟨10793267000644864574620567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57564090670105944397976357 10793267000644864574620567)
              ·
                refine ⟨16189900500967296861930851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10793267000644864574620567 16189900500967296861930851)
                ·
                  refine ⟨24284850751450945292896277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16189900500967296861930851 24284850751450945292896277)
                  ·
                    refine ⟨1138352378974263060604513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24284850751450945292896277 1138352378974263060604513)
                    ·
                      rfl

theorem cell22_3325400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_3325400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325400 prefixEnd_3325400 := by exact prefixLift 3325400
  have htrace : WordTrace (prefixWord ++ tailWord_3325400) baseStart_3325400 baseEnd_3325400 := by
    simpa [prefixWord, tailWord_3325400, baseEnd_3325400] using wordTrace_append hprefix tailTrace_3325400
  have hstable : (prefixWord ++ tailWord_3325400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325400).length < 2 ^ (prefixWord ++ tailWord_3325400).sum := by decide
  have hdescent : baseEnd_3325400 < baseStart_3325400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325402 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_3325402 : Nat := 118140960795 + 3325402 * 2 ^ 59
def prefixEnd_3325402 : Nat := 4983230072969 + 3 ^ 40 * 3325402 * 2
def baseEnd_3325402 : Nat := 1138353063615135722054507

theorem tailTrace_3325402 : CollatzResearch.WordTrace tailWord_3325402 prefixEnd_3325402 1138353063615135722054507 := by
  unfold tailWord_3325402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30321843774660990572804615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80858250065762641527478973 30321843774660990572804615)
  ·
    refine ⟨45482765661991485859206923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30321843774660990572804615 45482765661991485859206923)
    ·
      refine ⟨68224148492987228788810385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45482765661991485859206923 68224148492987228788810385)
      ·
        refine ⟨51168111369740421591607789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68224148492987228788810385 51168111369740421591607789)
        ·
          refine ⟨19188041763652658096852921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51168111369740421591607789 19188041763652658096852921)
          ·
            refine ⟨14391031322739493572639691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19188041763652658096852921 14391031322739493572639691)
            ·
              refine ⟨21586546984109240358959537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14391031322739493572639691 21586546984109240358959537)
              ·
                refine ⟨16189910238081930269219653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21586546984109240358959537 16189910238081930269219653)
                ·
                  refine ⟨3035608169640361925478685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16189910238081930269219653 3035608169640361925478685)
                  ·
                    refine ⟨1138353063615135722054507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035608169640361925478685 1138353063615135722054507)
                    ·
                      rfl

theorem cell22_3325402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_3325402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325402 prefixEnd_3325402 := by exact prefixLift 3325402
  have htrace : WordTrace (prefixWord ++ tailWord_3325402) baseStart_3325402 baseEnd_3325402 := by
    simpa [prefixWord, tailWord_3325402, baseEnd_3325402] using wordTrace_append hprefix tailTrace_3325402
  have hstable : (prefixWord ++ tailWord_3325402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325402).length < 2 ^ (prefixWord ++ tailWord_3325402).sum := by decide
  have hdescent : baseEnd_3325402 < baseStart_3325402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325415 : List Nat := [1, 1, 5, 2, 1, 2, 10]
def baseStart_3325415 : Nat := 118140960795 + 3325415 * 2 ^ 59
def prefixEnd_3325415 : Nat := 4983230072969 + 3 ^ 40 * 3325415 * 2
def baseEnd_3325415 : Nat := 42161389399289185980721

theorem tailTrace_3325415 : CollatzResearch.WordTrace tailWord_3325415 prefixEnd_3325415 42161389399289185980721 := by
  unfold tailWord_3325415
  simp only [CollatzResearch.WordTrace]
  refine ⟨121287849247596865511441699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80858566165064577007627799 121287849247596865511441699)
  ·
    refine ⟨181931773871395298267162549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121287849247596865511441699 181931773871395298267162549)
    ·
      refine ⟨17056103800443309212546489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181931773871395298267162549 17056103800443309212546489)
      ·
        refine ⟨12792077850332481909409867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17056103800443309212546489 12792077850332481909409867)
        ·
          refine ⟨19188116775498722864114801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792077850332481909409867 19188116775498722864114801)
          ·
            refine ⟨14391087581624042148086101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19188116775498722864114801 14391087581624042148086101)
            ·
              refine ⟨42161389399289185980721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14391087581624042148086101 42161389399289185980721)
              ·
                rfl

theorem cell22_3325415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 10].length) (baseStart_3325415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325415 prefixEnd_3325415 := by exact prefixLift 3325415
  have htrace : WordTrace (prefixWord ++ tailWord_3325415) baseStart_3325415 baseEnd_3325415 := by
    simpa [prefixWord, tailWord_3325415, baseEnd_3325415] using wordTrace_append hprefix tailTrace_3325415
  have hstable : (prefixWord ++ tailWord_3325415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325415).length < 2 ^ (prefixWord ++ tailWord_3325415).sum := by decide
  have hdescent : baseEnd_3325415 < baseStart_3325415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325421 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3325421 : Nat := 118140960795 + 3325421 * 2 ^ 59
def prefixEnd_3325421 : Nat := 4983230072969 + 3 ^ 40 * 3325421 * 2
def baseEnd_3325421 : Nat := 379453189234475335276483

theorem tailTrace_3325421 : CollatzResearch.WordTrace tailWord_3325421 prefixEnd_3325421 379453189234475335276483 := by
  unfold tailWord_3325421
  simp only [CollatzResearch.WordTrace]
  refine ⟨121288068085575128536160117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80858712057050085690773411 121288068085575128536160117)
  ·
    refine ⟨11370756383022668300265011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121288068085575128536160117 11370756383022668300265011)
    ·
      refine ⟨17056134574534002450397517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11370756383022668300265011 17056134574534002450397517)
      ·
        refine ⟨6396050465450250918899069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17056134574534002450397517 6396050465450250918899069)
        ·
          refine ⟨2398518924543844094587151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6396050465450250918899069 2398518924543844094587151)
          ·
            refine ⟨3597778386815766141880727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398518924543844094587151 3597778386815766141880727)
            ·
              refine ⟨5396667580223649212821091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597778386815766141880727 5396667580223649212821091)
              ·
                refine ⟨8095001370335473819231637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5396667580223649212821091 8095001370335473819231637)
                ·
                  refine ⟨379453189234475335276483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8095001370335473819231637 379453189234475335276483)
                  ·
                    rfl

theorem cell22_3325421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3325421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325421 prefixEnd_3325421 := by exact prefixLift 3325421
  have htrace : WordTrace (prefixWord ++ tailWord_3325421) baseStart_3325421 baseEnd_3325421 := by
    simpa [prefixWord, tailWord_3325421, baseEnd_3325421] using wordTrace_append hprefix tailTrace_3325421
  have hstable : (prefixWord ++ tailWord_3325421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325421).length < 2 ^ (prefixWord ++ tailWord_3325421).sum := by decide
  have hdescent : baseEnd_3325421 < baseStart_3325421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325524 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3325524 : Nat := 118140960795 + 3325524 * 2 ^ 59
def prefixEnd_3325524 : Nat := 4983230072969 + 3 ^ 40 * 3325524 * 2
def baseEnd_3325524 : Nat := 1138394826708368070504133

theorem tailTrace_3325524 : CollatzResearch.WordTrace tailWord_3325524 prefixEnd_3325524 1138394826708368070504133 := by
  unfold tailWord_3325524
  simp only [CollatzResearch.WordTrace]
  refine ⟨60645912402100988563579813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80861216536134651418106417 60645912402100988563579813)
  ·
    refine ⟨11371108575393935355671215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60645912402100988563579813 11371108575393935355671215)
    ·
      refine ⟨17056662863090903033506823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11371108575393935355671215 17056662863090903033506823)
      ·
        refine ⟨25584994294636354550260235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17056662863090903033506823 25584994294636354550260235)
        ·
          refine ⟨38377491441954531825390353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25584994294636354550260235 38377491441954531825390353)
          ·
            refine ⟨28783118581465898869042765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38377491441954531825390353 28783118581465898869042765)
            ·
              refine ⟨10793669468049712075891037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28783118581465898869042765 10793669468049712075891037)
              ·
                refine ⟨4047626050518642028459139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10793669468049712075891037 4047626050518642028459139)
                ·
                  refine ⟨6071439075777963042688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047626050518642028459139 6071439075777963042688709)
                  ·
                    refine ⟨1138394826708368070504133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6071439075777963042688709 1138394826708368070504133)
                    ·
                      rfl

theorem cell22_3325524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3325524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325524 prefixEnd_3325524 := by exact prefixLift 3325524
  have htrace : WordTrace (prefixWord ++ tailWord_3325524) baseStart_3325524 baseEnd_3325524 := by
    simpa [prefixWord, tailWord_3325524, baseEnd_3325524] using wordTrace_append hprefix tailTrace_3325524
  have hstable : (prefixWord ++ tailWord_3325524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325524).length < 2 ^ (prefixWord ++ tailWord_3325524).sum := by decide
  have hdescent : baseEnd_3325524 < baseStart_3325524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325539 : List Nat := [1, 1, 1, 5, 1, 3, 2, 4, 4]
def baseStart_3325539 : Nat := 118140960795 + 3325539 * 2 ^ 59
def prefixEnd_3325539 : Nat := 4983230072969 + 3 ^ 40 * 3325539 * 2
def baseEnd_3325539 : Nat := 379466653838304343793029

theorem tailTrace_3325539 : CollatzResearch.WordTrace tailWord_3325539 prefixEnd_3325539 379466653838304343793029 := by
  unfold tailWord_3325539
  simp only [CollatzResearch.WordTrace]
  refine ⟨121292371899147634688955671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80861581266098423125970447 121292371899147634688955671)
  ·
    refine ⟨181938557848721452033433507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121292371899147634688955671 181938557848721452033433507)
    ·
      refine ⟨272907836773082178050150261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181938557848721452033433507 272907836773082178050150261)
      ·
        refine ⟨25585109697476454192201587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272907836773082178050150261 25585109697476454192201587)
        ·
          refine ⟨38377664546214681288302381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25585109697476454192201587 38377664546214681288302381)
          ·
            refine ⟨14391624204830505483113393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38377664546214681288302381 14391624204830505483113393)
            ·
              refine ⟨10793718153622879112335045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14391624204830505483113393 10793718153622879112335045)
              ·
                refine ⟨2023822153804289833562821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10793718153622879112335045 2023822153804289833562821)
                ·
                  refine ⟨379466653838304343793029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023822153804289833562821 379466653838304343793029)
                  ·
                    rfl

theorem cell22_3325539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 4].length) (baseStart_3325539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325539 prefixEnd_3325539 := by exact prefixLift 3325539
  have htrace : WordTrace (prefixWord ++ tailWord_3325539) baseStart_3325539 baseEnd_3325539 := by
    simpa [prefixWord, tailWord_3325539, baseEnd_3325539] using wordTrace_append hprefix tailTrace_3325539
  have hstable : (prefixWord ++ tailWord_3325539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325539).length < 2 ^ (prefixWord ++ tailWord_3325539).sum := by decide
  have hdescent : baseEnd_3325539 < baseStart_3325539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325552 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_3325552 : Nat := 118140960795 + 3325552 * 2 ^ 59
def prefixEnd_3325552 : Nat := 4983230072969 + 3 ^ 40 * 3325552 * 2
def baseEnd_3325552 : Nat := 1138404411680585330804047

theorem tailTrace_3325552 : CollatzResearch.WordTrace tailWord_3325552 prefixEnd_3325552 1138404411680585330804047 := by
  unfold tailWord_3325552
  simp only [CollatzResearch.WordTrace]
  refine ⟨60646423024050268954589455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80861897365400358606119273 60646423024050268954589455)
  ·
    refine ⟨90969634536075403431884183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60646423024050268954589455 90969634536075403431884183)
    ·
      refine ⟨136454451804113105147826275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90969634536075403431884183 136454451804113105147826275)
      ·
        refine ⟨204681677706169657721739413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136454451804113105147826275 204681677706169657721739413)
        ·
          refine ⟨9594453642476702705706535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204681677706169657721739413 9594453642476702705706535)
          ·
            refine ⟨14391680463715054058559803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9594453642476702705706535 14391680463715054058559803)
            ·
              refine ⟨21587520695572581087839705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14391680463715054058559803 21587520695572581087839705)
              ·
                refine ⟨16190640521679435815879779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21587520695572581087839705 16190640521679435815879779)
                ·
                  refine ⟨24285960782519153723819669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16190640521679435815879779 24285960782519153723819669)
                  ·
                    refine ⟨1138404411680585330804047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24285960782519153723819669 1138404411680585330804047)
                    ·
                      rfl

theorem cell22_3325552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_3325552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325552 prefixEnd_3325552 := by exact prefixLift 3325552
  have htrace : WordTrace (prefixWord ++ tailWord_3325552) baseStart_3325552 baseEnd_3325552 := by
    simpa [prefixWord, tailWord_3325552, baseEnd_3325552] using wordTrace_append hprefix tailTrace_3325552
  have hstable : (prefixWord ++ tailWord_3325552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325552).length < 2 ^ (prefixWord ++ tailWord_3325552).sum := by decide
  have hdescent : baseEnd_3325552 < baseStart_3325552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325554 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_3325554 : Nat := 118140960795 + 3325554 * 2 ^ 59
def prefixEnd_3325554 : Nat := 4983230072969 + 3 ^ 40 * 3325554 * 2
def baseEnd_3325554 : Nat := 1138405096321457992254041

theorem tailTrace_3325554 : CollatzResearch.WordTrace tailWord_3325554 prefixEnd_3325554 1138405096321457992254041 := by
  unfold tailWord_3325554
  simp only [CollatzResearch.WordTrace]
  refine ⟨30323229748523323062687929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80861945996062194833834477 30323229748523323062687929)
  ·
    refine ⟨22742422311392492297015947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30323229748523323062687929 22742422311392492297015947)
    ·
      refine ⟨34113633467088738445523921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22742422311392492297015947 34113633467088738445523921)
      ·
        refine ⟨25585225100316553834142941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34113633467088738445523921 25585225100316553834142941)
        ·
          refine ⟨9594459412618707687803603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25585225100316553834142941 9594459412618707687803603)
          ·
            refine ⟨14391689118928061531705405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9594459412618707687803603 14391689118928061531705405)
            ·
              refine ⟨5396883419598023074389527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14391689118928061531705405 5396883419598023074389527)
              ·
                refine ⟨8095325129397034611584291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5396883419598023074389527 8095325129397034611584291)
                ·
                  refine ⟨12142987694095551917376437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095325129397034611584291 12142987694095551917376437)
                  ·
                    refine ⟨1138405096321457992254041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12142987694095551917376437 1138405096321457992254041)
                    ·
                      rfl

theorem cell22_3325554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_3325554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325554 prefixEnd_3325554 := by exact prefixLift 3325554
  have htrace : WordTrace (prefixWord ++ tailWord_3325554) baseStart_3325554 baseEnd_3325554 := by
    simpa [prefixWord, tailWord_3325554, baseEnd_3325554] using wordTrace_append hprefix tailTrace_3325554
  have hstable : (prefixWord ++ tailWord_3325554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325554).length < 2 ^ (prefixWord ++ tailWord_3325554).sum := by decide
  have hdescent : baseEnd_3325554 < baseStart_3325554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325586 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3325586 : Nat := 118140960795 + 3325586 * 2 ^ 59
def prefixEnd_3325586 : Nat := 4983230072969 + 3 ^ 40 * 3325586 * 2
def baseEnd_3325586 : Nat := 1138416050575420575453943

theorem tailTrace_3325586 : CollatzResearch.WordTrace tailWord_3325586 prefixEnd_3325586 1138416050575420575453943 := by
  unfold tailWord_3325586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30323521532494340428979153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80862724086651574477277741 30323521532494340428979153)
  ·
    refine ⟨22742641149370755321734365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30323521532494340428979153 22742641149370755321734365)
    ·
      refine ⟨8528490431014033245650387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22742641149370755321734365 8528490431014033245650387)
      ·
        refine ⟨12792735646521049868475581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528490431014033245650387 12792735646521049868475581)
        ·
          refine ⟨4797275867445393700678343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12792735646521049868475581 4797275867445393700678343)
          ·
            refine ⟨7195913801168090551017515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4797275867445393700678343 7195913801168090551017515)
            ·
              refine ⟨10793870701752135826526273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7195913801168090551017515 10793870701752135826526273)
              ·
                refine ⟨8095403026314101869894705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10793870701752135826526273 8095403026314101869894705)
                ·
                  refine ⟨6071552269735576402421029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8095403026314101869894705 6071552269735576402421029)
                  ·
                    refine ⟨1138416050575420575453943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6071552269735576402421029 1138416050575420575453943)
                    ·
                      rfl

theorem cell22_3325586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3325586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325586 prefixEnd_3325586 := by exact prefixLift 3325586
  have htrace : WordTrace (prefixWord ++ tailWord_3325586) baseStart_3325586 baseEnd_3325586 := by
    simpa [prefixWord, tailWord_3325586, baseEnd_3325586] using wordTrace_append hprefix tailTrace_3325586
  have hstable : (prefixWord ++ tailWord_3325586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325586).length < 2 ^ (prefixWord ++ tailWord_3325586).sum := by decide
  have hdescent : baseEnd_3325586 < baseStart_3325586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325597 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_3325597 : Nat := 118140960795 + 3325597 * 2 ^ 59
def prefixEnd_3325597 : Nat := 4983230072969 + 3 ^ 40 * 3325597 * 2
def baseEnd_3325597 : Nat := 1138419816100220213428909

theorem tailTrace_3325597 : CollatzResearch.WordTrace tailWord_3325597 prefixEnd_3325597 1138419816100220213428909 := by
  unfold tailWord_3325597
  simp only [CollatzResearch.WordTrace]
  refine ⟨121294487332937510594567045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80862991555291673729711363 121294487332937510594567045)
  ·
    refine ⟨22742716374925783236481321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121294487332937510594567045 22742716374925783236481321)
    ·
      refine ⟨17057037281194337427360991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22742716374925783236481321 17057037281194337427360991)
      ·
        refine ⟨25585555921791506141041487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17057037281194337427360991 25585555921791506141041487)
        ·
          refine ⟨38378333882687259211562231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25585555921791506141041487 38378333882687259211562231)
          ·
            refine ⟨57567500824030888817343347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38378333882687259211562231 57567500824030888817343347)
            ·
              refine ⟨86351251236046333226015021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57567500824030888817343347 86351251236046333226015021)
              ·
                refine ⟨32381719213517374959755633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86351251236046333226015021 32381719213517374959755633)
                ·
                  refine ⟨24286289410138031219816725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32381719213517374959755633 24286289410138031219816725)
                  ·
                    refine ⟨1138419816100220213428909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24286289410138031219816725 1138419816100220213428909)
                    ·
                      rfl

theorem cell22_3325597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_3325597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325597 prefixEnd_3325597 := by exact prefixLift 3325597
  have htrace : WordTrace (prefixWord ++ tailWord_3325597) baseStart_3325597 baseEnd_3325597 := by
    simpa [prefixWord, tailWord_3325597, baseEnd_3325597] using wordTrace_append hprefix tailTrace_3325597
  have hstable : (prefixWord ++ tailWord_3325597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325597).length < 2 ^ (prefixWord ++ tailWord_3325597).sum := by decide
  have hdescent : baseEnd_3325597 < baseStart_3325597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325650 : List Nat := [3, 2, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_3325650 : Nat := 118140960795 + 3325650 * 2 ^ 59
def prefixEnd_3325650 : Nat := 4983230072969 + 3 ^ 40 * 3325650 * 2
def baseEnd_3325650 : Nat := 1138437959083345741853747

theorem tailTrace_3325650 : CollatzResearch.WordTrace tailWord_3325650 prefixEnd_3325650 1138437959083345741853747 := by
  unfold tailWord_3325650
  simp only [CollatzResearch.WordTrace]
  refine ⟨30324105100436375161561601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80864280267830333764164269 30324105100436375161561601)
  ·
    refine ⟨22743078825327281371171201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30324105100436375161561601 22743078825327281371171201)
    ·
      refine ⟨17057309118995461028378401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22743078825327281371171201 17057309118995461028378401)
      ·
        refine ⟨12792981839246595771283801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17057309118995461028378401 12792981839246595771283801)
        ·
          refine ⟨9594736379434946828462851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12792981839246595771283801 9594736379434946828462851)
          ·
            refine ⟨14392104569152420242694277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9594736379434946828462851 14392104569152420242694277)
            ·
              refine ⟨2698519606716078795505177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14392104569152420242694277 2698519606716078795505177)
              ·
                refine ⟨2023889705037059096628883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698519606716078795505177 2023889705037059096628883)
                ·
                  refine ⟨3035834557555588644943325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023889705037059096628883 3035834557555588644943325)
                  ·
                    refine ⟨1138437959083345741853747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035834557555588644943325 1138437959083345741853747)
                    ·
                      rfl

theorem cell22_3325650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_3325650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325650 prefixEnd_3325650 := by exact prefixLift 3325650
  have htrace : WordTrace (prefixWord ++ tailWord_3325650) baseStart_3325650 baseEnd_3325650 := by
    simpa [prefixWord, tailWord_3325650, baseEnd_3325650] using wordTrace_append hprefix tailTrace_3325650
  have hstable : (prefixWord ++ tailWord_3325650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325650).length < 2 ^ (prefixWord ++ tailWord_3325650).sum := by decide
  have hdescent : baseEnd_3325650 < baseStart_3325650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325704 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3325704 : Nat := 118140960795 + 3325704 * 2 ^ 59
def prefixEnd_3325704 : Nat := 4983230072969 + 3 ^ 40 * 3325704 * 2
def baseEnd_3325704 : Nat := 1138456444386907601003581

theorem tailTrace_3325704 : CollatzResearch.WordTrace tailWord_3325704 prefixEnd_3325704 1138456444386907601003581 := by
  unfold tailWord_3325704
  simp only [CollatzResearch.WordTrace]
  refine ⟨60649194971774933934356083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80865593295699911912474777 60649194971774933934356083)
  ·
    refine ⟨90973792457662400901534125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60649194971774933934356083 90973792457662400901534125)
    ·
      refine ⟨34115172171623400338075297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90973792457662400901534125 34115172171623400338075297)
      ·
        refine ⟨25586379128717550253556473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34115172171623400338075297 25586379128717550253556473)
        ·
          refine ⟨19189784346538162690167355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25586379128717550253556473 19189784346538162690167355)
          ·
            refine ⟨28784676519807244035251033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19189784346538162690167355 28784676519807244035251033)
            ·
              refine ⟨21588507389855433026438275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28784676519807244035251033 21588507389855433026438275)
              ·
                refine ⟨32382761084783149539657413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21588507389855433026438275 32382761084783149539657413)
                ·
                  refine ⟨6071767703396840538685765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32382761084783149539657413 6071767703396840538685765)
                  ·
                    refine ⟨1138456444386907601003581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6071767703396840538685765 1138456444386907601003581)
                    ·
                      rfl

theorem cell22_3325704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3325704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325704 prefixEnd_3325704 := by exact prefixLift 3325704
  have htrace : WordTrace (prefixWord ++ tailWord_3325704) baseStart_3325704 baseEnd_3325704 := by
    simpa [prefixWord, tailWord_3325704, baseEnd_3325704] using wordTrace_append hprefix tailTrace_3325704
  have hstable : (prefixWord ++ tailWord_3325704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325704).length < 2 ^ (prefixWord ++ tailWord_3325704).sum := by decide
  have hdescent : baseEnd_3325704 < baseStart_3325704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
