import V185TrunkScan22Chunk015

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_141935 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 1, 6]
def baseStart_141935 : Nat := 118140960795 + 141935 * 2 ^ 59
def prefixEnd_141935 : Nat := 4983230072969 + 3 ^ 40 * 141935 * 2
def baseEnd_141935 : Nat := 48587251130671608239839

theorem tailTrace_141935 : CollatzResearch.WordTrace tailWord_141935 prefixEnd_141935 48587251130671608239839 := by
  unfold tailWord_141935
  simp only [CollatzResearch.WordTrace]
  refine ⟨5176794740801210413219259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3451196493867473608812839 5176794740801210413219259)
  ·
    refine ⟨7765192111201815619828889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5176794740801210413219259 7765192111201815619828889)
    ·
      refine ⟨5823894083401361714871667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7765192111201815619828889 5823894083401361714871667)
      ·
        refine ⟨8735841125102042572307501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5823894083401361714871667 8735841125102042572307501)
        ·
          refine ⟨3275940421913265964615313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8735841125102042572307501 3275940421913265964615313)
          ·
            refine ⟨2456955316434949473461485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3275940421913265964615313 2456955316434949473461485)
            ·
              refine ⟨921358243663106052548057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2456955316434949473461485 921358243663106052548057)
              ·
                refine ⟨691018682747329539411043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921358243663106052548057 691018682747329539411043)
                ·
                  refine ⟨1036528024120994309116565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691018682747329539411043 1036528024120994309116565)
                  ·
                    refine ⟨48587251130671608239839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1036528024120994309116565 48587251130671608239839)
                    ·
                      rfl

theorem cell22_141935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_141935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141935 prefixEnd_141935 := by exact prefixLift 141935
  have htrace : WordTrace (prefixWord ++ tailWord_141935) baseStart_141935 baseEnd_141935 := by
    simpa [prefixWord, tailWord_141935, baseEnd_141935] using wordTrace_append hprefix tailTrace_141935
  have hstable : (prefixWord ++ tailWord_141935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141935).length < 2 ^ (prefixWord ++ tailWord_141935).sum := by decide
  have hdescent : baseEnd_141935 < baseStart_141935 := by decide
  rcases family_descends (prefixWord ++ tailWord_141935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141941 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_141941 : Nat := 118140960795 + 141941 * 2 ^ 59
def prefixEnd_141941 : Nat := 4983230072969 + 3 ^ 40 * 141941 * 2
def baseEnd_141941 : Nat := 48589305053289592589821

theorem tailTrace_141941 : CollatzResearch.WordTrace tailWord_141941 prefixEnd_141941 48589305053289592589821 := by
  unfold tailWord_141941
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177013578779473437937677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3451342385852982291958451 5177013578779473437937677)
  ·
    refine ⟨1941380092042302539226629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5177013578779473437937677 1941380092042302539226629)
    ·
      refine ⟨364008767257931726104993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1941380092042302539226629 364008767257931726104993)
      ·
        refine ⟨273006575443448794578745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364008767257931726104993 273006575443448794578745)
        ·
          refine ⟨204754931582586595934059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273006575443448794578745 204754931582586595934059)
          ·
            refine ⟨307132397373879893901089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204754931582586595934059 307132397373879893901089)
            ·
              refine ⟨230349298030409920425817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307132397373879893901089 230349298030409920425817)
              ·
                refine ⟨172761973522807440319363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230349298030409920425817 172761973522807440319363)
                ·
                  refine ⟨259142960284211160479045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172761973522807440319363 259142960284211160479045)
                  ·
                    refine ⟨48589305053289592589821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 259142960284211160479045 48589305053289592589821)
                    ·
                      rfl

theorem cell22_141941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_141941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141941 prefixEnd_141941 := by exact prefixLift 141941
  have htrace : WordTrace (prefixWord ++ tailWord_141941) baseStart_141941 baseEnd_141941 := by
    simpa [prefixWord, tailWord_141941, baseEnd_141941] using wordTrace_append hprefix tailTrace_141941
  have hstable : (prefixWord ++ tailWord_141941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141941).length < 2 ^ (prefixWord ++ tailWord_141941).sum := by decide
  have hdescent : baseEnd_141941 < baseStart_141941 := by decide
  rcases family_descends (prefixWord ++ tailWord_141941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141956 : List Nat := [2, 3, 2, 1, 3, 3, 1, 3, 4]
def baseStart_141956 : Nat := 118140960795 + 141956 * 2 ^ 59
def prefixEnd_141956 : Nat := 4983230072969 + 3 ^ 40 * 141956 * 2
def baseEnd_141956 : Nat := 16198146619944851154925

theorem tailTrace_141956 : CollatzResearch.WordTrace tailWord_141956 prefixEnd_141956 16198146619944851154925 := by
  unfold tailWord_141956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588780336862565499866861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3451707115816753999822481 2588780336862565499866861)
  ·
    refine ⟨970792626323462062450073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2588780336862565499866861 970792626323462062450073)
    ·
      refine ⟨728094469742596546837555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 970792626323462062450073 728094469742596546837555)
      ·
        refine ⟨1092141704613894820256333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728094469742596546837555 1092141704613894820256333)
        ·
          refine ⟨409553139230210557596125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1092141704613894820256333 409553139230210557596125)
          ·
            refine ⟨153582427211328959098547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 409553139230210557596125 153582427211328959098547)
            ·
              refine ⟨230373640816993438647821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153582427211328959098547 230373640816993438647821)
              ·
                refine ⟨86390115306372539492933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230373640816993438647821 86390115306372539492933)
                ·
                  refine ⟨16198146619944851154925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86390115306372539492933 16198146619944851154925)
                  ·
                    rfl

theorem cell22_141956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_141956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_141956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_141956 prefixEnd_141956 := by exact prefixLift 141956
  have htrace : WordTrace (prefixWord ++ tailWord_141956) baseStart_141956 baseEnd_141956 := by
    simpa [prefixWord, tailWord_141956, baseEnd_141956] using wordTrace_append hprefix tailTrace_141956
  have hstable : (prefixWord ++ tailWord_141956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141956).length < 2 ^ (prefixWord ++ tailWord_141956).sum := by decide
  have hdescent : baseEnd_141956 < baseStart_141956 := by decide
  rcases family_descends (prefixWord ++ tailWord_141956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142042 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_142042 : Nat := 118140960795 + 142042 * 2 ^ 59
def prefixEnd_142042 : Nat := 4983230072969 + 3 ^ 40 * 142042 * 2
def baseEnd_142042 : Nat := 48623879417358995814511

theorem tailTrace_142042 : CollatzResearch.WordTrace tailWord_142042 prefixEnd_142042 48623879417358995814511 := by
  unfold tailWord_142042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295174337853391921841095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3453798234275711791576253 1295174337853391921841095)
  ·
    refine ⟨1942761506780087882761643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1295174337853391921841095 1942761506780087882761643)
    ·
      refine ⟨2914142260170131824142465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942761506780087882761643 2914142260170131824142465)
      ·
        refine ⟨2185606695127598868106849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2914142260170131824142465 2185606695127598868106849)
        ·
          refine ⟨1639205021345699151080137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2185606695127598868106849 1639205021345699151080137)
          ·
            refine ⟨1229403766009274363310103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639205021345699151080137 1229403766009274363310103)
            ·
              refine ⟨1844105649013911544965155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229403766009274363310103 1844105649013911544965155)
              ·
                refine ⟨2766158473520867317447733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844105649013911544965155 2766158473520867317447733)
                ·
                  refine ⟨259327356892581311010725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2766158473520867317447733 259327356892581311010725)
                  ·
                    refine ⟨48623879417358995814511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 259327356892581311010725 48623879417358995814511)
                    ·
                      rfl

theorem cell22_142042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_142042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142042 prefixEnd_142042 := by exact prefixLift 142042
  have htrace : WordTrace (prefixWord ++ tailWord_142042) baseStart_142042 baseEnd_142042 := by
    simpa [prefixWord, tailWord_142042, baseEnd_142042] using wordTrace_append hprefix tailTrace_142042
  have hstable : (prefixWord ++ tailWord_142042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142042).length < 2 ^ (prefixWord ++ tailWord_142042).sum := by decide
  have hdescent : baseEnd_142042 < baseStart_142042 := by decide
  rcases family_descends (prefixWord ++ tailWord_142042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142044 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_142044 : Nat := 118140960795 + 142044 * 2 ^ 59
def prefixEnd_142044 : Nat := 4983230072969 + 3 ^ 40 * 142044 * 2
def baseEnd_142044 : Nat := 48624564058231657264505

theorem tailTrace_142044 : CollatzResearch.WordTrace tailWord_142044 prefixEnd_142044 48624564058231657264505 := by
  unfold tailWord_142044
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590385148703161014468593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3453846864937548019291457 2590385148703161014468593)
  ·
    refine ⟨1942788861527370760851445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2590385148703161014468593 1942788861527370760851445)
    ·
      refine ⟨182136455768191008829823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1942788861527370760851445 182136455768191008829823)
      ·
        refine ⟨273204683652286513244735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182136455768191008829823 273204683652286513244735)
        ·
          refine ⟨409807025478429769867103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273204683652286513244735 409807025478429769867103)
          ·
            refine ⟨614710538217644654800655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409807025478429769867103 614710538217644654800655)
            ·
              refine ⟨922065807326466982200983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614710538217644654800655 922065807326466982200983)
              ·
                refine ⟨1383098710989700473301475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922065807326466982200983 1383098710989700473301475)
                ·
                  refine ⟨2074648066484550709952213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383098710989700473301475 2074648066484550709952213)
                  ·
                    refine ⟨48624564058231657264505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2074648066484550709952213 48624564058231657264505)
                    ·
                      rfl

theorem cell22_142044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_142044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142044 prefixEnd_142044 := by exact prefixLift 142044
  have htrace : WordTrace (prefixWord ++ tailWord_142044) baseStart_142044 baseEnd_142044 := by
    simpa [prefixWord, tailWord_142044, baseEnd_142044] using wordTrace_append hprefix tailTrace_142044
  have hstable : (prefixWord ++ tailWord_142044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142044).length < 2 ^ (prefixWord ++ tailWord_142044).sum := by decide
  have hdescent : baseEnd_142044 < baseStart_142044 := by decide
  rcases family_descends (prefixWord ++ tailWord_142044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142072 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_142072 : Nat := 118140960795 + 142072 * 2 ^ 59
def prefixEnd_142072 : Nat := 4983230072969 + 3 ^ 40 * 142072 * 2
def baseEnd_142072 : Nat := 48634149030448917564419

theorem tailTrace_142072 : CollatzResearch.WordTrace tailWord_142072 prefixEnd_142072 48634149030448917564419 := by
  unfold tailWord_142072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590895770652441405478235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3454527694203255207304313 2590895770652441405478235)
  ·
    refine ⟨3886343655978662108217353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2590895770652441405478235 3886343655978662108217353)
    ·
      refine ⟨2914757741983996581163015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3886343655978662108217353 2914757741983996581163015)
      ·
        refine ⟨4372136612975994871744523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914757741983996581163015 4372136612975994871744523)
        ·
          refine ⟨6558204919463992307616785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372136612975994871744523 6558204919463992307616785)
          ·
            refine ⟨4918653689597994230712589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6558204919463992307616785 4918653689597994230712589)
            ·
              refine ⟨1844495133599247836517221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4918653689597994230712589 1844495133599247836517221)
              ·
                refine ⟨345842837549858969346979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1844495133599247836517221 345842837549858969346979)
                ·
                  refine ⟨518764256324788454020469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345842837549858969346979 518764256324788454020469)
                  ·
                    refine ⟨48634149030448917564419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 518764256324788454020469 48634149030448917564419)
                    ·
                      rfl

theorem cell22_142072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_142072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142072 prefixEnd_142072 := by exact prefixLift 142072
  have htrace : WordTrace (prefixWord ++ tailWord_142072) baseStart_142072 baseEnd_142072 := by
    simpa [prefixWord, tailWord_142072, baseEnd_142072] using wordTrace_append hprefix tailTrace_142072
  have hstable : (prefixWord ++ tailWord_142072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142072).length < 2 ^ (prefixWord ++ tailWord_142072).sum := by decide
  have hdescent : baseEnd_142072 < baseStart_142072 := by decide
  rcases family_descends (prefixWord ++ tailWord_142072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142074 : List Nat := [3, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_142074 : Nat := 118140960795 + 142074 * 2 ^ 59
def prefixEnd_142074 : Nat := 4983230072969 + 3 ^ 40 * 142074 * 2
def baseEnd_142074 : Nat := 16211611223773859671471

theorem tailTrace_142074 : CollatzResearch.WordTrace tailWord_142074 prefixEnd_142074 16211611223773859671471 := by
  unfold tailWord_142074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295466121824409288132319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3454576324865091435019517 1295466121824409288132319)
  ·
    refine ⟨1943199182736613932198479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1295466121824409288132319 1943199182736613932198479)
    ·
      refine ⟨2914798774104920898297719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943199182736613932198479 2914798774104920898297719)
      ·
        refine ⟨4372198161157381347446579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914798774104920898297719 4372198161157381347446579)
        ·
          refine ⟨6558297241736072021169869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372198161157381347446579 6558297241736072021169869)
          ·
            refine ⟨2459361465651027007938701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6558297241736072021169869 2459361465651027007938701)
            ·
              refine ⟨922260549619135127977013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2459361465651027007938701 922260549619135127977013)
              ·
                refine ⟨86461926526793918247845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 922260549619135127977013 86461926526793918247845)
                ·
                  refine ⟨16211611223773859671471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86461926526793918247845 16211611223773859671471)
                  ·
                    rfl

theorem cell22_142074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_142074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142074 prefixEnd_142074 := by exact prefixLift 142074
  have htrace : WordTrace (prefixWord ++ tailWord_142074) baseStart_142074 baseEnd_142074 := by
    simpa [prefixWord, tailWord_142074, baseEnd_142074] using wordTrace_append hprefix tailTrace_142074
  have hstable : (prefixWord ++ tailWord_142074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142074).length < 2 ^ (prefixWord ++ tailWord_142074).sum := by decide
  have hdescent : baseEnd_142074 < baseStart_142074 := by decide
  rcases family_descends (prefixWord ++ tailWord_142074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142076 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_142076 : Nat := 118140960795 + 142076 * 2 ^ 59
def prefixEnd_142076 : Nat := 4983230072969 + 3 ^ 40 * 142076 * 2
def baseEnd_142076 : Nat := 48635518312194240464407

theorem tailTrace_142076 : CollatzResearch.WordTrace tailWord_142076 prefixEnd_142076 48635518312194240464407 := by
  unfold tailWord_142076
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590968716645195747051041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3454624955526927662734721 2590968716645195747051041)
  ·
    refine ⟨1943226537483896810288281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2590968716645195747051041 1943226537483896810288281)
    ·
      refine ⟨1457419903112922607716211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1943226537483896810288281 1457419903112922607716211)
      ·
        refine ⟨2186129854669383911574317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457419903112922607716211 2186129854669383911574317)
        ·
          refine ⟨819798695501018966840369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2186129854669383911574317 819798695501018966840369)
          ·
            refine ⟨614849021625764225130277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819798695501018966840369 614849021625764225130277)
            ·
              refine ⟨115284191554830792211927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 614849021625764225130277 115284191554830792211927)
              ·
                refine ⟨172926287332246188317891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115284191554830792211927 172926287332246188317891)
                ·
                  refine ⟨259389430998369282476837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172926287332246188317891 259389430998369282476837)
                  ·
                    refine ⟨48635518312194240464407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 259389430998369282476837 48635518312194240464407)
                    ·
                      rfl

theorem cell22_142076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_142076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142076 prefixEnd_142076 := by exact prefixLift 142076
  have htrace : WordTrace (prefixWord ++ tailWord_142076) baseStart_142076 baseEnd_142076 := by
    simpa [prefixWord, tailWord_142076, baseEnd_142076] using wordTrace_append hprefix tailTrace_142076
  have hstable : (prefixWord ++ tailWord_142076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142076).length < 2 ^ (prefixWord ++ tailWord_142076).sum := by decide
  have hdescent : baseEnd_142076 < baseStart_142076 := by decide
  rcases family_descends (prefixWord ++ tailWord_142076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142117 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_142117 : Nat := 118140960795 + 142117 * 2 ^ 59
def prefixEnd_142117 : Nat := 4983230072969 + 3 ^ 40 * 142117 * 2
def baseEnd_142117 : Nat := 48649553450083800189281

theorem tailTrace_142117 : CollatzResearch.WordTrace tailWord_142117 prefixEnd_142117 48649553450083800189281 := by
  unfold tailWord_142117
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183432826141855496344605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3455621884094570330896403 5183432826141855496344605)
  ·
    refine ⟨1943787309803195811129227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5183432826141855496344605 1943787309803195811129227)
    ·
      refine ⟨2915680964704793716693841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943787309803195811129227 2915680964704793716693841)
      ·
        refine ⟨2186760723528595287520381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2915680964704793716693841 2186760723528595287520381)
        ·
          refine ⟨820035271323223232820143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2186760723528595287520381 820035271323223232820143)
          ·
            refine ⟨1230052906984834849230215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820035271323223232820143 1230052906984834849230215)
            ·
              refine ⟨1845079360477252273845323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230052906984834849230215 1845079360477252273845323)
              ·
                refine ⟨2767619040715878410767985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845079360477252273845323 2767619040715878410767985)
                ·
                  refine ⟨2075714280536908808075989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2767619040715878410767985 2075714280536908808075989)
                  ·
                    refine ⟨48649553450083800189281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2075714280536908808075989 48649553450083800189281)
                    ·
                      rfl

theorem cell22_142117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_142117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142117 prefixEnd_142117 := by exact prefixLift 142117
  have htrace : WordTrace (prefixWord ++ tailWord_142117) baseStart_142117 baseEnd_142117 := by
    simpa [prefixWord, tailWord_142117, baseEnd_142117] using wordTrace_append hprefix tailTrace_142117
  have hstable : (prefixWord ++ tailWord_142117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142117).length < 2 ^ (prefixWord ++ tailWord_142117).sum := by decide
  have hdescent : baseEnd_142117 < baseStart_142117 := by decide
  rcases family_descends (prefixWord ++ tailWord_142117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142147 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 7]
def baseStart_142147 : Nat := 118140960795 + 142147 * 2 ^ 59
def prefixEnd_142147 : Nat := 4983230072969 + 3 ^ 40 * 142147 * 2
def baseEnd_142147 : Nat := 16219941021057907313063

theorem tailTrace_142147 : CollatzResearch.WordTrace tailWord_142147 prefixEnd_142147 16219941021057907313063 := by
  unfold tailWord_142147
  simp only [CollatzResearch.WordTrace]
  refine ⟨5184527016033170619936695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3456351344022113746624463 5184527016033170619936695)
  ·
    refine ⟨7776790524049755929905043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5184527016033170619936695 7776790524049755929905043)
    ·
      refine ⟨11665185786074633894857565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7776790524049755929905043 11665185786074633894857565)
      ·
        refine ⟨4374444669777987710571587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11665185786074633894857565 4374444669777987710571587)
        ·
          refine ⟨6561667004666981565857381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374444669777987710571587 6561667004666981565857381)
          ·
            refine ⟨1230312563375059043598259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6561667004666981565857381 1230312563375059043598259)
            ·
              refine ⟨1845468845062588565397389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230312563375059043598259 1845468845062588565397389)
              ·
                refine ⟨692050816898470712024021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1845468845062588565397389 692050816898470712024021)
                ·
                  refine ⟨16219941021057907313063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 692050816898470712024021 16219941021057907313063)
                  ·
                    rfl

theorem cell22_142147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_142147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142147 prefixEnd_142147 := by exact prefixLift 142147
  have htrace : WordTrace (prefixWord ++ tailWord_142147) baseStart_142147 baseEnd_142147 := by
    simpa [prefixWord, tailWord_142147, baseEnd_142147] using wordTrace_append hprefix tailTrace_142147
  have hstable : (prefixWord ++ tailWord_142147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142147).length < 2 ^ (prefixWord ++ tailWord_142147).sum := by decide
  have hdescent : baseEnd_142147 < baseStart_142147 := by decide
  rcases family_descends (prefixWord ++ tailWord_142147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142157 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_142157 : Nat := 118140960795 + 142157 * 2 ^ 59
def prefixEnd_142157 : Nat := 4983230072969 + 3 ^ 40 * 142157 * 2
def baseEnd_142157 : Nat := 48663246267537029189159

theorem tailTrace_142157 : CollatzResearch.WordTrace tailWord_142157 prefixEnd_142157 48663246267537029189159 := by
  unfold tailWord_142157
  simp only [CollatzResearch.WordTrace]
  refine ⟨5184891745996942327800725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3456594497331294885200483 5184891745996942327800725)
  ·
    refine ⟨243041800593606671615659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5184891745996942327800725 243041800593606671615659)
    ·
      refine ⟨364562700890410007423489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243041800593606671615659 364562700890410007423489)
      ·
        refine ⟨273422025667807505567617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364562700890410007423489 273422025667807505567617)
        ·
          refine ⟨205066519250855629175713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273422025667807505567617 205066519250855629175713)
          ·
            refine ⟨153799889438141721881785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205066519250855629175713 153799889438141721881785)
            ·
              refine ⟨115349917078606291411339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153799889438141721881785 115349917078606291411339)
              ·
                refine ⟨173024875617909437117009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115349917078606291411339 173024875617909437117009)
                ·
                  refine ⟨129768656713432077837757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173024875617909437117009 129768656713432077837757)
                  ·
                    refine ⟨48663246267537029189159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129768656713432077837757 48663246267537029189159)
                    ·
                      rfl

theorem cell22_142157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_142157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142157 prefixEnd_142157 := by exact prefixLift 142157
  have htrace : WordTrace (prefixWord ++ tailWord_142157) baseStart_142157 baseEnd_142157 := by
    simpa [prefixWord, tailWord_142157, baseEnd_142157] using wordTrace_append hprefix tailTrace_142157
  have hstable : (prefixWord ++ tailWord_142157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142157).length < 2 ^ (prefixWord ++ tailWord_142157).sum := by decide
  have hdescent : baseEnd_142157 < baseStart_142157 := by decide
  rcases family_descends (prefixWord ++ tailWord_142157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142198 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_142198 : Nat := 118140960795 + 142198 * 2 ^ 59
def prefixEnd_142198 : Nat := 4983230072969 + 3 ^ 40 * 142198 * 2
def baseEnd_142198 : Nat := 16225760468475529638011

theorem tailTrace_142198 : CollatzResearch.WordTrace tailWord_142198 prefixEnd_142198 16225760468475529638011 := by
  unfold tailWord_142198
  simp only [CollatzResearch.WordTrace]
  refine ⟨324149196178025395627703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3457591425898937553362165 324149196178025395627703)
  ·
    refine ⟨486223794267038093441555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 324149196178025395627703 486223794267038093441555)
    ·
      refine ⟨729335691400557140162333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 486223794267038093441555 729335691400557140162333)
      ·
        refine ⟨273500884275208927560875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 729335691400557140162333 273500884275208927560875)
        ·
          refine ⟨410251326412813391341313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273500884275208927560875 410251326412813391341313)
          ·
            refine ⟨307688494809610043505985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410251326412813391341313 307688494809610043505985)
            ·
              refine ⟨230766371107207532629489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307688494809610043505985 230766371107207532629489)
              ·
                refine ⟨173074778330405649472117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230766371107207532629489 173074778330405649472117)
                ·
                  refine ⟨16225760468475529638011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173074778330405649472117 16225760468475529638011)
                  ·
                    rfl

theorem cell22_142198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_142198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142198 prefixEnd_142198 := by exact prefixLift 142198
  have htrace : WordTrace (prefixWord ++ tailWord_142198) baseStart_142198 baseEnd_142198 := by
    simpa [prefixWord, tailWord_142198, baseEnd_142198] using wordTrace_append hprefix tailTrace_142198
  have hstable : (prefixWord ++ tailWord_142198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142198).length < 2 ^ (prefixWord ++ tailWord_142198).sum := by decide
  have hdescent : baseEnd_142198 < baseStart_142198 := by decide
  rcases family_descends (prefixWord ++ tailWord_142198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142241 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_142241 : Nat := 118140960795 + 142241 * 2 ^ 59
def prefixEnd_142241 : Nat := 4983230072969 + 3 ^ 40 * 142241 * 2
def baseEnd_142241 : Nat := 48692001184188810088901

theorem tailTrace_142241 : CollatzResearch.WordTrace tailWord_142241 prefixEnd_142241 48692001184188810088901 := by
  unfold tailWord_142241
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187955477692624673858577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3458636985128416449239051 5187955477692624673858577)
  ·
    refine ⟨3890966608269468505393933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5187955477692624673858577 3890966608269468505393933)
    ·
      refine ⟨1459112478101050689522725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3890966608269468505393933 1459112478101050689522725)
      ·
        refine ⟨273583589643947004285511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1459112478101050689522725 273583589643947004285511)
        ·
          refine ⟨410375384465920506428267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273583589643947004285511 410375384465920506428267)
          ·
            refine ⟨615563076698880759642401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410375384465920506428267 615563076698880759642401)
            ·
              refine ⟨461672307524160569731801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615563076698880759642401 461672307524160569731801)
              ·
                refine ⟨346254230643120427298851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461672307524160569731801 346254230643120427298851)
                ·
                  refine ⟨519381345964680640948277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346254230643120427298851 519381345964680640948277)
                  ·
                    refine ⟨48692001184188810088901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 519381345964680640948277 48692001184188810088901)
                    ·
                      rfl

theorem cell22_142241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_142241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142241 prefixEnd_142241 := by exact prefixLift 142241
  have htrace : WordTrace (prefixWord ++ tailWord_142241) baseStart_142241 baseEnd_142241 := by
    simpa [prefixWord, tailWord_142241, baseEnd_142241] using wordTrace_append hprefix tailTrace_142241
  have hstable : (prefixWord ++ tailWord_142241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142241).length < 2 ^ (prefixWord ++ tailWord_142241).sum := by decide
  have hdescent : baseEnd_142241 < baseStart_142241 := by decide
  rcases family_descends (prefixWord ++ tailWord_142241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142260 : List Nat := [2, 5, 2, 1, 1, 1, 2, 4, 4]
def baseStart_142260 : Nat := 118140960795 + 142260 * 2 ^ 59
def prefixEnd_142260 : Nat := 4983230072969 + 3 ^ 40 * 142260 * 2
def baseEnd_142260 : Nat := 16232835090826364621281

theorem tailTrace_142260 : CollatzResearch.WordTrace tailWord_142260 prefixEnd_142260 16232835090826364621281 := by
  unfold tailWord_142260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594324232311895459400117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3459098976415860612533489 2594324232311895459400117)
  ·
    refine ⟨243217896779240199318761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2594324232311895459400117 243217896779240199318761)
    ·
      refine ⟨182413422584430149489071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243217896779240199318761 182413422584430149489071)
      ·
        refine ⟨273620133876645224233607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182413422584430149489071 273620133876645224233607)
        ·
          refine ⟨410430200814967836350411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273620133876645224233607 410430200814967836350411)
          ·
            refine ⟨615645301222451754525617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410430200814967836350411 615645301222451754525617)
            ·
              refine ⟨461733975916838815894213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615645301222451754525617 461733975916838815894213)
              ·
                refine ⟨86575120484407277980165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461733975916838815894213 86575120484407277980165)
                ·
                  refine ⟨16232835090826364621281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86575120484407277980165 16232835090826364621281)
                  ·
                    rfl

theorem cell22_142260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_142260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142260 prefixEnd_142260 := by exact prefixLift 142260
  have htrace : WordTrace (prefixWord ++ tailWord_142260) baseStart_142260 baseEnd_142260 := by
    simpa [prefixWord, tailWord_142260, baseEnd_142260] using wordTrace_append hprefix tailTrace_142260
  have hstable : (prefixWord ++ tailWord_142260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142260).length < 2 ^ (prefixWord ++ tailWord_142260).sum := by decide
  have hdescent : baseEnd_142260 < baseStart_142260 := by decide
  rcases family_descends (prefixWord ++ tailWord_142260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142393 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_142393 : Nat := 118140960795 + 142393 * 2 ^ 59
def prefixEnd_142393 : Nat := 4983230072969 + 3 ^ 40 * 142393 * 2
def baseEnd_142393 : Nat := 48744033890511080288435

theorem tailTrace_142393 : CollatzResearch.WordTrace tailWord_142393 prefixEnd_142393 48744033890511080288435 := by
  unfold tailWord_142393
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193499373141954633391833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3462332915427969755594555 5193499373141954633391833)
  ·
    refine ⟨3895124529856465975043875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5193499373141954633391833 3895124529856465975043875)
    ·
      refine ⟨5842686794784698962565813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3895124529856465975043875 5842686794784698962565813)
      ·
        refine ⟨547751887011065527740545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5842686794784698962565813 547751887011065527740545)
        ·
          refine ⟨410813915258299145805409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547751887011065527740545 410813915258299145805409)
          ·
            refine ⟨308110436443724359354057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410813915258299145805409 308110436443724359354057)
            ·
              refine ⟨231082827332793269515543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308110436443724359354057 231082827332793269515543)
              ·
                refine ⟨346624240999189904273315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231082827332793269515543 346624240999189904273315)
                ·
                  refine ⟨519936361498784856409973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346624240999189904273315 519936361498784856409973)
                  ·
                    refine ⟨48744033890511080288435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 519936361498784856409973 48744033890511080288435)
                    ·
                      rfl

theorem cell22_142393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_142393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142393 prefixEnd_142393 := by exact prefixLift 142393
  have htrace : WordTrace (prefixWord ++ tailWord_142393) baseStart_142393 baseEnd_142393 := by
    simpa [prefixWord, tailWord_142393, baseEnd_142393] using wordTrace_append hprefix tailTrace_142393
  have hstable : (prefixWord ++ tailWord_142393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142393).length < 2 ^ (prefixWord ++ tailWord_142393).sum := by decide
  have hdescent : baseEnd_142393 < baseStart_142393 := by decide
  rcases family_descends (prefixWord ++ tailWord_142393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142575 : List Nat := [1, 1, 2, 1, 7, 1, 3, 6]
def baseStart_142575 : Nat := 118140960795 + 142575 * 2 ^ 59
def prefixEnd_142575 : Nat := 4983230072969 + 3 ^ 40 * 142575 * 2
def baseEnd_142575 : Nat := 5422926245547030248653

theorem tailTrace_142575 : CollatzResearch.WordTrace tailWord_142575 prefixEnd_142575 5422926245547030248653 := by
  unfold tailWord_142575
  simp only [CollatzResearch.WordTrace]
  refine ⟨5200137458482599716517179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3466758305655066477678119 5200137458482599716517179)
  ·
    refine ⟨7800206187723899574775769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5200137458482599716517179 7800206187723899574775769)
    ·
      refine ⟨5850154640792924681081827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7800206187723899574775769 5850154640792924681081827)
      ·
        refine ⟨8775231961189387021622741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850154640792924681081827 8775231961189387021622741)
        ·
          refine ⟨205669499090376258319283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8775231961189387021622741 205669499090376258319283)
          ·
            refine ⟨308504248635564387478925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205669499090376258319283 308504248635564387478925)
            ·
              refine ⟨115689093238336645304597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 308504248635564387478925 115689093238336645304597)
              ·
                refine ⟨5422926245547030248653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115689093238336645304597 5422926245547030248653)
                ·
                  rfl

theorem cell22_142575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 6].length) (baseStart_142575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142575 prefixEnd_142575 := by exact prefixLift 142575
  have htrace : WordTrace (prefixWord ++ tailWord_142575) baseStart_142575 baseEnd_142575 := by
    simpa [prefixWord, tailWord_142575, baseEnd_142575] using wordTrace_append hprefix tailTrace_142575
  have hstable : (prefixWord ++ tailWord_142575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142575).length < 2 ^ (prefixWord ++ tailWord_142575).sum := by decide
  have hdescent : baseEnd_142575 < baseStart_142575 := by decide
  rcases family_descends (prefixWord ++ tailWord_142575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142603 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 7]
def baseStart_142603 : Nat := 118140960795 + 142603 * 2 ^ 59
def prefixEnd_142603 : Nat := 4983230072969 + 3 ^ 40 * 142603 * 2
def baseEnd_142603 : Nat := 16271973727380177512597

theorem tailTrace_142603 : CollatzResearch.WordTrace tailWord_142603 prefixEnd_142603 16271973727380177512597 := by
  unfold tailWord_142603
  simp only [CollatzResearch.WordTrace]
  refine ⟨5201158702381160498536463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3467439134920773665690975 5201158702381160498536463)
  ·
    refine ⟨7801738053571740747804695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5201158702381160498536463 7801738053571740747804695)
    ·
      refine ⟨11702607080357611121707043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7801738053571740747804695 11702607080357611121707043)
      ·
        refine ⟨17553910620536416682560565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11702607080357611121707043 17553910620536416682560565)
        ·
          refine ⟨1645679120675289063990053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17553910620536416682560565 1645679120675289063990053)
          ·
            refine ⟨308564835126616699498135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1645679120675289063990053 308564835126616699498135)
            ·
              refine ⟨462847252689925049247203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308564835126616699498135 462847252689925049247203)
              ·
                refine ⟨694270879034887573870805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462847252689925049247203 694270879034887573870805)
                ·
                  refine ⟨16271973727380177512597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 694270879034887573870805 16271973727380177512597)
                  ·
                    rfl

theorem cell22_142603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 7].length) (baseStart_142603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142603 prefixEnd_142603 := by exact prefixLift 142603
  have htrace : WordTrace (prefixWord ++ tailWord_142603) baseStart_142603 baseEnd_142603 := by
    simpa [prefixWord, tailWord_142603, baseEnd_142603] using wordTrace_append hprefix tailTrace_142603
  have hstable : (prefixWord ++ tailWord_142603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142603).length < 2 ^ (prefixWord ++ tailWord_142603).sum := by decide
  have hdescent : baseEnd_142603 < baseStart_142603 := by decide
  rcases family_descends (prefixWord ++ tailWord_142603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142650 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_142650 : Nat := 118140960795 + 142650 * 2 ^ 59
def prefixEnd_142650 : Nat := 4983230072969 + 3 ^ 40 * 142650 * 2
def baseEnd_142650 : Nat := 48832010242648076612647

theorem tailTrace_142650 : CollatzResearch.WordTrace tailWord_142650 prefixEnd_142650 48832010242648076612647 := by
  unfold tailWord_142650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300718233302721881374351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3468581955473925016998269 1300718233302721881374351)
  ·
    refine ⟨1951077349954082822061527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1300718233302721881374351 1951077349954082822061527)
    ·
      refine ⟨2926616024931124233092291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951077349954082822061527 2926616024931124233092291)
      ·
        refine ⟨4389924037396686349638437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2926616024931124233092291 4389924037396686349638437)
        ·
          refine ⟨823110757011878690557207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4389924037396686349638437 823110757011878690557207)
          ·
            refine ⟨1234666135517818035835811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823110757011878690557207 1234666135517818035835811)
            ·
              refine ⟨1851999203276727053753717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234666135517818035835811 1851999203276727053753717)
              ·
                refine ⟨173624925307193161289411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1851999203276727053753717 173624925307193161289411)
                ·
                  refine ⟨260437387960789741934117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173624925307193161289411 260437387960789741934117)
                  ·
                    refine ⟨48832010242648076612647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 260437387960789741934117 48832010242648076612647)
                    ·
                      rfl

theorem cell22_142650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_142650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142650 prefixEnd_142650 := by exact prefixLift 142650
  have htrace : WordTrace (prefixWord ++ tailWord_142650) baseStart_142650 baseEnd_142650 := by
    simpa [prefixWord, tailWord_142650, baseEnd_142650] using wordTrace_append hprefix tailTrace_142650
  have hstable : (prefixWord ++ tailWord_142650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142650).length < 2 ^ (prefixWord ++ tailWord_142650).sum := by decide
  have hdescent : baseEnd_142650 < baseStart_142650 := by decide
  rcases family_descends (prefixWord ++ tailWord_142650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142665 : List Nat := [1, 2, 1, 1, 2, 3, 2, 6, 4]
def baseStart_142665 : Nat := 118140960795 + 142665 * 2 ^ 59
def prefixEnd_142665 : Nat := 4983230072969 + 3 ^ 40 * 142665 * 2
def baseEnd_142665 : Nat := 16279048349731012495867

theorem tailTrace_142665 : CollatzResearch.WordTrace tailWord_142665 prefixEnd_142665 16279048349731012495867 := by
  unfold tailWord_142665
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203420028156545087293449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3468946685437696724862299 5203420028156545087293449)
  ·
    refine ⟨3902565021117408815470087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5203420028156545087293449 3902565021117408815470087)
    ·
      refine ⟨5853847531676113223205131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3902565021117408815470087 5853847531676113223205131)
      ·
        refine ⟨8780771297514169834807697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5853847531676113223205131 8780771297514169834807697)
        ·
          refine ⟨6585578473135627376105773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8780771297514169834807697 6585578473135627376105773)
          ·
            refine ⟨2469591927425860266039665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6585578473135627376105773 2469591927425860266039665)
            ·
              refine ⟨1852193945569395199529749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469591927425860266039665 1852193945569395199529749)
              ·
                refine ⟨86821591198565399977957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1852193945569395199529749 86821591198565399977957)
                ·
                  refine ⟨16279048349731012495867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86821591198565399977957 16279048349731012495867)
                  ·
                    rfl

theorem cell22_142665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_142665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142665 prefixEnd_142665 := by exact prefixLift 142665
  have htrace : WordTrace (prefixWord ++ tailWord_142665) baseStart_142665 baseEnd_142665 := by
    simpa [prefixWord, tailWord_142665, baseEnd_142665] using wordTrace_append hprefix tailTrace_142665
  have hstable : (prefixWord ++ tailWord_142665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142665).length < 2 ^ (prefixWord ++ tailWord_142665).sum := by decide
  have hdescent : baseEnd_142665 < baseStart_142665 := by decide
  rcases family_descends (prefixWord ++ tailWord_142665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142693 : List Nat := [1, 3, 1, 3, 1, 2, 1, 10]
def baseStart_142693 : Nat := 118140960795 + 142693 * 2 ^ 59
def prefixEnd_142693 : Nat := 4983230072969 + 3 ^ 40 * 142693 * 2
def baseEnd_142693 : Nat := 5427414446823366420835

theorem tailTrace_142693 : CollatzResearch.WordTrace tailWord_142693 prefixEnd_142693 5427414446823366420835 := by
  unfold tailWord_142693
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204441272055105869312733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3469627514703403912875155 5204441272055105869312733)
  ·
    refine ⟨1951665477020664700992275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5204441272055105869312733 1951665477020664700992275)
    ·
      refine ⟨2927498215530997051488413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951665477020664700992275 2927498215530997051488413)
      ·
        refine ⟨1097811830824123894308155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2927498215530997051488413 1097811830824123894308155)
        ·
          refine ⟨1646717746236185841462233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097811830824123894308155 1646717746236185841462233)
          ·
            refine ⟨1235038309677139381096675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646717746236185841462233 1235038309677139381096675)
            ·
              refine ⟨1852557464515709071645013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235038309677139381096675 1852557464515709071645013)
              ·
                refine ⟨5427414446823366420835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1852557464515709071645013 5427414446823366420835)
                ·
                  rfl

theorem cell22_142693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 10].length) (baseStart_142693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142693 prefixEnd_142693 := by exact prefixLift 142693
  have htrace : WordTrace (prefixWord ++ tailWord_142693) baseStart_142693 baseEnd_142693 := by
    simpa [prefixWord, tailWord_142693, baseEnd_142693] using wordTrace_append hprefix tailTrace_142693
  have hstable : (prefixWord ++ tailWord_142693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142693).length < 2 ^ (prefixWord ++ tailWord_142693).sum := by decide
  have hdescent : baseEnd_142693 < baseStart_142693 := by decide
  rcases family_descends (prefixWord ++ tailWord_142693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142815 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 3, 5]
def baseStart_142815 : Nat := 118140960795 + 142815 * 2 ^ 59
def prefixEnd_142815 : Nat := 4983230072969 + 3 ^ 40 * 142815 * 2
def baseEnd_142815 : Nat := 48888493114642646237141

theorem tailTrace_142815 : CollatzResearch.WordTrace tailWord_142815 prefixEnd_142815 48888493114642646237141 := by
  unfold tailWord_142815
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208890977613120705253899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3472593985075413803502599 5208890977613120705253899)
  ·
    refine ⟨7813336466419681057880849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5208890977613120705253899 7813336466419681057880849)
    ·
      refine ⟨5860002349814760793410637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7813336466419681057880849 5860002349814760793410637)
      ·
        refine ⟨2197500881180535297528989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5860002349814760793410637 2197500881180535297528989)
        ·
          refine ⟨824062830442700736573371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2197500881180535297528989 824062830442700736573371)
          ·
            refine ⟨1236094245664051104860057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824062830442700736573371 1236094245664051104860057)
            ·
              refine ⟨927070684248038328645043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236094245664051104860057 927070684248038328645043)
              ·
                refine ⟨1390606026372057492967565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927070684248038328645043 1390606026372057492967565)
                ·
                  refine ⟨521477259889521559862837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1390606026372057492967565 521477259889521559862837)
                  ·
                    refine ⟨48888493114642646237141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 521477259889521559862837 48888493114642646237141)
                    ·
                      rfl

theorem cell22_142815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_142815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142815 prefixEnd_142815 := by exact prefixLift 142815
  have htrace : WordTrace (prefixWord ++ tailWord_142815) baseStart_142815 baseEnd_142815 := by
    simpa [prefixWord, tailWord_142815, baseEnd_142815] using wordTrace_append hprefix tailTrace_142815
  have hstable : (prefixWord ++ tailWord_142815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142815).length < 2 ^ (prefixWord ++ tailWord_142815).sum := by decide
  have hdescent : baseEnd_142815 < baseStart_142815 := by decide
  rcases family_descends (prefixWord ++ tailWord_142815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142832 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 4, 3]
def baseStart_142832 : Nat := 118140960795 + 142832 * 2 ^ 59
def prefixEnd_142832 : Nat := 4983230072969 + 3 ^ 40 * 142832 * 2
def baseEnd_142832 : Nat := 48894312562060268562089

theorem tailTrace_142832 : CollatzResearch.WordTrace tailWord_142832 prefixEnd_142832 48894312562060268562089 := by
  unfold tailWord_142832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604755509275766304311375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3473007345701021739081833 2604755509275766304311375)
  ·
    refine ⟨3907133263913649456467063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2604755509275766304311375 3907133263913649456467063)
    ·
      refine ⟨5860699895870474184700595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3907133263913649456467063 5860699895870474184700595)
      ·
        refine ⟨8791049843805711277050893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5860699895870474184700595 8791049843805711277050893)
        ·
          refine ⟨3296643691427141728894085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8791049843805711277050893 3296643691427141728894085)
          ·
            refine ⟨618120692142589074167641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3296643691427141728894085 618120692142589074167641)
            ·
              refine ⟨463590519106941805625731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618120692142589074167641 463590519106941805625731)
              ·
                refine ⟨695385778660412708438597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463590519106941805625731 695385778660412708438597)
                ·
                  refine ⟨130384833498827382832237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695385778660412708438597 130384833498827382832237)
                  ·
                    refine ⟨48894312562060268562089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130384833498827382832237 48894312562060268562089)
                    ·
                      rfl

theorem cell22_142832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_142832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142832 prefixEnd_142832 := by exact prefixLift 142832
  have htrace : WordTrace (prefixWord ++ tailWord_142832) baseStart_142832 baseEnd_142832 := by
    simpa [prefixWord, tailWord_142832, baseEnd_142832] using wordTrace_append hprefix tailTrace_142832
  have hstable : (prefixWord ++ tailWord_142832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142832).length < 2 ^ (prefixWord ++ tailWord_142832).sum := by decide
  have hdescent : baseEnd_142832 < baseStart_142832 := by decide
  rcases family_descends (prefixWord ++ tailWord_142832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142834 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_142834 : Nat := 118140960795 + 142834 * 2 ^ 59
def prefixEnd_142834 : Nat := 4983230072969 + 3 ^ 40 * 142834 * 2
def baseEnd_142834 : Nat := 16298332400977643337361

theorem tailTrace_142834 : CollatzResearch.WordTrace tailWord_142834 prefixEnd_142834 16298332400977643337361 := by
  unfold tailWord_142834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302395991136071737548889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3473055976362857966797037 1302395991136071737548889)
  ·
    refine ⟨976796993352053803161667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1302395991136071737548889 976796993352053803161667)
    ·
      refine ⟨1465195490028080704742501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976796993352053803161667 1465195490028080704742501)
      ·
        refine ⟨274724154380265132139219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1465195490028080704742501 274724154380265132139219)
        ·
          refine ⟨412086231570397698208829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274724154380265132139219 412086231570397698208829)
          ·
            refine ⟨154532336838899136828311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 412086231570397698208829 154532336838899136828311)
            ·
              refine ⟨231798505258348705242467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154532336838899136828311 231798505258348705242467)
              ·
                refine ⟨347697757887523057863701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231798505258348705242467 347697757887523057863701)
                ·
                  refine ⟨16298332400977643337361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 347697757887523057863701 16298332400977643337361)
                  ·
                    rfl

theorem cell22_142834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_142834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142834 prefixEnd_142834 := by exact prefixLift 142834
  have htrace : WordTrace (prefixWord ++ tailWord_142834) baseStart_142834 baseEnd_142834 := by
    simpa [prefixWord, tailWord_142834, baseEnd_142834] using wordTrace_append hprefix tailTrace_142834
  have hstable : (prefixWord ++ tailWord_142834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142834).length < 2 ^ (prefixWord ++ tailWord_142834).sum := by decide
  have hdescent : baseEnd_142834 < baseStart_142834 := by decide
  rcases family_descends (prefixWord ++ tailWord_142834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142845 : List Nat := [1, 4, 1, 1, 1, 4, 1, 9]
def baseStart_142845 : Nat := 118140960795 + 142845 * 2 ^ 59
def prefixEnd_142845 : Nat := 4983230072969 + 3 ^ 40 * 142845 * 2
def baseEnd_142845 : Nat := 5433195858636951998561

theorem tailTrace_142845 : CollatzResearch.WordTrace tailWord_142845 prefixEnd_142845 5433195858636951998561 := by
  unfold tailWord_142845
  simp only [CollatzResearch.WordTrace]
  refine ⟨5209985167504435828845989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3473323445002957219230659 5209985167504435828845989)
  ·
    refine ⟨976872218907081717908623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5209985167504435828845989 976872218907081717908623)
    ·
      refine ⟨1465308328360622576862935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976872218907081717908623 1465308328360622576862935)
      ·
        refine ⟨2197962492540933865294403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465308328360622576862935 2197962492540933865294403)
        ·
          refine ⟨3296943738811400797941605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197962492540933865294403 3296943738811400797941605)
          ·
            refine ⟨618176951027137649614051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3296943738811400797941605 618176951027137649614051)
            ·
              refine ⟨927265426540706474421077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618176951027137649614051 927265426540706474421077)
              ·
                refine ⟨5433195858636951998561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 927265426540706474421077 5433195858636951998561)
                ·
                  rfl

theorem cell22_142845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 9].length) (baseStart_142845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142845 prefixEnd_142845 := by exact prefixLift 142845
  have htrace : WordTrace (prefixWord ++ tailWord_142845) baseStart_142845 baseEnd_142845 := by
    simpa [prefixWord, tailWord_142845, baseEnd_142845] using wordTrace_append hprefix tailTrace_142845
  have hstable : (prefixWord ++ tailWord_142845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142845).length < 2 ^ (prefixWord ++ tailWord_142845).sum := by decide
  have hdescent : baseEnd_142845 < baseStart_142845 := by decide
  rcases family_descends (prefixWord ++ tailWord_142845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142941 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 7]
def baseStart_142941 : Nat := 118140960795 + 142941 * 2 ^ 59
def prefixEnd_142941 : Nat := 4983230072969 + 3 ^ 40 * 142941 * 2
def baseEnd_142941 : Nat := 16310541829873439195585

theorem tailTrace_142941 : CollatzResearch.WordTrace tailWord_142941 prefixEnd_142941 16310541829873439195585 := by
  unfold tailWord_142941
  simp only [CollatzResearch.WordTrace]
  refine ⟨5213486575156644224340677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3475657716771096149560451 5213486575156644224340677)
  ·
    refine ⟨977528732841870792063877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5213486575156644224340677 977528732841870792063877)
    ·
      refine ⟨183286637407850773511977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 977528732841870792063877 183286637407850773511977)
      ·
        refine ⟨137464978055888080133983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183286637407850773511977 137464978055888080133983)
        ·
          refine ⟨206197467083832120200975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137464978055888080133983 206197467083832120200975)
          ·
            refine ⟨309296200625748180301463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206197467083832120200975 309296200625748180301463)
            ·
              refine ⟨463944300938622270452195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309296200625748180301463 463944300938622270452195)
              ·
                refine ⟨695916451407933405678293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463944300938622270452195 695916451407933405678293)
                ·
                  refine ⟨16310541829873439195585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 695916451407933405678293 16310541829873439195585)
                  ·
                    rfl

theorem cell22_142941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_142941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142941 prefixEnd_142941 := by exact prefixLift 142941
  have htrace : WordTrace (prefixWord ++ tailWord_142941) baseStart_142941 baseEnd_142941 := by
    simpa [prefixWord, tailWord_142941, baseEnd_142941] using wordTrace_append hprefix tailTrace_142941
  have hstable : (prefixWord ++ tailWord_142941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142941).length < 2 ^ (prefixWord ++ tailWord_142941).sum := by decide
  have hdescent : baseEnd_142941 < baseStart_142941 := by decide
  rcases family_descends (prefixWord ++ tailWord_142941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142986 : List Nat := [3, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_142986 : Nat := 118140960795 + 142986 * 2 ^ 59
def prefixEnd_142986 : Nat := 4983230072969 + 3 ^ 40 * 142986 * 2
def baseEnd_142986 : Nat := 16315676636418400070539

theorem tailTrace_142986 : CollatzResearch.WordTrace tailWord_142986 prefixEnd_142986 16315676636418400070539 := by
  unfold tailWord_142986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303781964998404227432203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3476751906662411273152541 1303781964998404227432203)
  ·
    refine ⟨1955672947497606341148305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1303781964998404227432203 1955672947497606341148305)
    ·
      refine ⟨1466754710623204755861229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1955672947497606341148305 1466754710623204755861229)
      ·
        refine ⟨550033016483701783447961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1466754710623204755861229 550033016483701783447961)
        ·
          refine ⟨412524762362776337585971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550033016483701783447961 412524762362776337585971)
          ·
            refine ⟨618787143544164506378957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412524762362776337585971 618787143544164506378957)
            ·
              refine ⟨232045178829061689892109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 618787143544164506378957 232045178829061689892109)
              ·
                refine ⟨87016942060898133709541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232045178829061689892109 87016942060898133709541)
                ·
                  refine ⟨16315676636418400070539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87016942060898133709541 16315676636418400070539)
                  ·
                    rfl

theorem cell22_142986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_142986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142986 prefixEnd_142986 := by exact prefixLift 142986
  have htrace : WordTrace (prefixWord ++ tailWord_142986) baseStart_142986 baseEnd_142986 := by
    simpa [prefixWord, tailWord_142986, baseEnd_142986] using wordTrace_append hprefix tailTrace_142986
  have hstable : (prefixWord ++ tailWord_142986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142986).length < 2 ^ (prefixWord ++ tailWord_142986).sum := by decide
  have hdescent : baseEnd_142986 < baseStart_142986 := by decide
  rcases family_descends (prefixWord ++ tailWord_142986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142999 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 2, 4]
def baseStart_142999 : Nat := 118140960795 + 142999 * 2 ^ 59
def prefixEnd_142999 : Nat := 4983230072969 + 3 ^ 40 * 142999 * 2
def baseEnd_142999 : Nat := 48951480074927499636577

theorem tailTrace_142999 : CollatzResearch.WordTrace tailWord_142999 prefixEnd_142999 48951480074927499636577 := by
  unfold tailWord_142999
  simp only [CollatzResearch.WordTrace]
  refine ⟨5215602008946520129952051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3477068005964346753301367 5215602008946520129952051)
  ·
    refine ⟨7823403013419780194928077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5215602008946520129952051 7823403013419780194928077)
    ·
      refine ⟨2933776130032417573098029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7823403013419780194928077 2933776130032417573098029)
      ·
        refine ⟨1100166048762156589911761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2933776130032417573098029 1100166048762156589911761)
        ·
          refine ⟨825124536571617442433821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1100166048762156589911761 825124536571617442433821)
          ·
            refine ⟨309421701214356540912683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 825124536571617442433821 309421701214356540912683)
            ·
              refine ⟨464132551821534811369025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309421701214356540912683 464132551821534811369025)
              ·
                refine ⟨348099413866151108526769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464132551821534811369025 348099413866151108526769)
                ·
                  refine ⟨261074560399613331395077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348099413866151108526769 261074560399613331395077)
                  ·
                    refine ⟨48951480074927499636577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261074560399613331395077 48951480074927499636577)
                    ·
                      rfl

theorem cell22_142999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_142999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_142999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_142999 prefixEnd_142999 := by exact prefixLift 142999
  have htrace : WordTrace (prefixWord ++ tailWord_142999) baseStart_142999 baseEnd_142999 := by
    simpa [prefixWord, tailWord_142999, baseEnd_142999] using wordTrace_append hprefix tailTrace_142999
  have hstable : (prefixWord ++ tailWord_142999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142999).length < 2 ^ (prefixWord ++ tailWord_142999).sum := by decide
  have hdescent : baseEnd_142999 < baseStart_142999 := by decide
  rcases family_descends (prefixWord ++ tailWord_142999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143089 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_143089 : Nat := 118140960795 + 143089 * 2 ^ 59
def prefixEnd_143089 : Nat := 4983230072969 + 3 ^ 40 * 143089 * 2
def baseEnd_143089 : Nat := 48982288914197264886301

theorem tailTrace_143089 : CollatzResearch.WordTrace tailWord_143089 prefixEnd_143089 48982288914197264886301 := by
  unfold tailWord_143089
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218884578620465500728321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3479256385746977000485547 5218884578620465500728321)
  ·
    refine ⟨3914163433965349125546241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5218884578620465500728321 3914163433965349125546241)
    ·
      refine ⟨2935622575474011844159681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3914163433965349125546241 2935622575474011844159681)
      ·
        refine ⟨2201716931605508883119761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935622575474011844159681 2201716931605508883119761)
        ·
          refine ⟨1651287698704131662339821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2201716931605508883119761 1651287698704131662339821)
          ·
            refine ⟨619232887014049373377433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1651287698704131662339821 619232887014049373377433)
            ·
              refine ⟨464424665260537030033075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619232887014049373377433 464424665260537030033075)
              ·
                refine ⟨696636997890805545049613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464424665260537030033075 696636997890805545049613)
                ·
                  refine ⟨261238874209052079393605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696636997890805545049613 261238874209052079393605)
                  ·
                    refine ⟨48982288914197264886301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261238874209052079393605 48982288914197264886301)
                    ·
                      rfl

theorem cell22_143089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_143089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143089 prefixEnd_143089 := by exact prefixLift 143089
  have htrace : WordTrace (prefixWord ++ tailWord_143089) baseStart_143089 baseEnd_143089 := by
    simpa [prefixWord, tailWord_143089, baseEnd_143089] using wordTrace_append hprefix tailTrace_143089
  have hstable : (prefixWord ++ tailWord_143089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143089).length < 2 ^ (prefixWord ++ tailWord_143089).sum := by decide
  have hdescent : baseEnd_143089 < baseStart_143089 := by decide
  rcases family_descends (prefixWord ++ tailWord_143089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143155 : List Nat := [1, 1, 1, 2, 8, 1, 1, 3, 4]
def baseStart_143155 : Nat := 118140960795 + 143155 * 2 ^ 59
def prefixEnd_143155 : Nat := 4983230072969 + 3 ^ 40 * 143155 * 2
def baseEnd_143155 : Nat := 16334960687665030912033

theorem tailTrace_143155 : CollatzResearch.WordTrace tailWord_143155 prefixEnd_143155 16334960687665030912033 := by
  unfold tailWord_143155
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221291796381358772630919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3480861197587572515087279 5221291796381358772630919)
  ·
    refine ⟨7831937694572038158946379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5221291796381358772630919 7831937694572038158946379)
    ·
      refine ⟨11747906541858057238419569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7831937694572038158946379 11747906541858057238419569)
      ·
        refine ⟨8810929906393542928814677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11747906541858057238419569 8810929906393542928814677)
        ·
          refine ⟨103253084840549331197047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 8810929906393542928814677 103253084840549331197047)
          ·
            refine ⟨154879627260823996795571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103253084840549331197047 154879627260823996795571)
            ·
              refine ⟨232319440891235995193357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154879627260823996795571 232319440891235995193357)
              ·
                refine ⟨87119790334213498197509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232319440891235995193357 87119790334213498197509)
                ·
                  refine ⟨16334960687665030912033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87119790334213498197509 16334960687665030912033)
                  ·
                    rfl

theorem cell22_143155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 4].length) (baseStart_143155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143155 prefixEnd_143155 := by exact prefixLift 143155
  have htrace : WordTrace (prefixWord ++ tailWord_143155) baseStart_143155 baseEnd_143155 := by
    simpa [prefixWord, tailWord_143155, baseEnd_143155] using wordTrace_append hprefix tailTrace_143155
  have hstable : (prefixWord ++ tailWord_143155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143155).length < 2 ^ (prefixWord ++ tailWord_143155).sum := by decide
  have hdescent : baseEnd_143155 < baseStart_143155 := by decide
  rcases family_descends (prefixWord ++ tailWord_143155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143166 : List Nat := [4, 2, 1, 2, 2, 3, 8]
def baseStart_143166 : Nat := 118140960795 + 143166 * 2 ^ 59
def prefixEnd_143166 : Nat := 4983230072969 + 3 ^ 40 * 143166 * 2
def baseEnd_143166 : Nat := 1815135095844249285595

theorem tailTrace_143166 : CollatzResearch.WordTrace tailWord_143166 prefixEnd_143166 1815135095844249285595 := by
  unfold tailWord_143166
  simp only [CollatzResearch.WordTrace]
  refine ⟨652711624917688456410169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3481128666227671767520901 652711624917688456410169)
  ·
    refine ⟨489533718688266342307627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 652711624917688456410169 489533718688266342307627)
    ·
      refine ⟨734300578032399513461441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489533718688266342307627 734300578032399513461441)
      ·
        refine ⟨550725433524299635096081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 734300578032399513461441 550725433524299635096081)
        ·
          refine ⟨413044075143224726322061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550725433524299635096081 413044075143224726322061)
          ·
            refine ⟨154891528178709272370773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 413044075143224726322061 154891528178709272370773)
            ·
              refine ⟨1815135095844249285595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 154891528178709272370773 1815135095844249285595)
              ·
                rfl

theorem cell22_143166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 8].length) (baseStart_143166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143166 prefixEnd_143166 := by exact prefixLift 143166
  have htrace : WordTrace (prefixWord ++ tailWord_143166) baseStart_143166 baseEnd_143166 := by
    simpa [prefixWord, tailWord_143166, baseEnd_143166] using wordTrace_append hprefix tailTrace_143166
  have hstable : (prefixWord ++ tailWord_143166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143166).length < 2 ^ (prefixWord ++ tailWord_143166).sum := by decide
  have hdescent : baseEnd_143166 < baseStart_143166 := by decide
  rcases family_descends (prefixWord ++ tailWord_143166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143299 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 4, 7]
def baseStart_143299 : Nat := 118140960795 + 143299 * 2 ^ 59
def prefixEnd_143299 : Nat := 4983230072969 + 3 ^ 40 * 143299 * 2
def baseEnd_143299 : Nat := 49054176205826717135657

theorem tailTrace_143299 : CollatzResearch.WordTrace tailWord_143299 prefixEnd_143299 49054176205826717135657 := by
  unfold tailWord_143299
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226543907859671365872951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3484362605239780910581967 5226543907859671365872951)
  ·
    refine ⟨7839815861789507048809427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5226543907859671365872951 7839815861789507048809427)
    ·
      refine ⟨11759723792684260573214141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7839815861789507048809427 11759723792684260573214141)
      ·
        refine ⟨4409896422256597714955303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11759723792684260573214141 4409896422256597714955303)
        ·
          refine ⟨6614844633384896572432955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409896422256597714955303 6614844633384896572432955)
          ·
            refine ⟨9922266950077344858649433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614844633384896572432955 9922266950077344858649433)
            ·
              refine ⟨7441700212558008643987075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9922266950077344858649433 7441700212558008643987075)
              ·
                refine ⟨11162550318837012965980613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441700212558008643987075 11162550318837012965980613)
                ·
                  refine ⟨2092978184781939931121365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11162550318837012965980613 2092978184781939931121365)
                  ·
                    refine ⟨49054176205826717135657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2092978184781939931121365 49054176205826717135657)
                    ·
                      rfl

theorem cell22_143299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_143299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143299 prefixEnd_143299 := by exact prefixLift 143299
  have htrace : WordTrace (prefixWord ++ tailWord_143299) baseStart_143299 baseEnd_143299 := by
    simpa [prefixWord, tailWord_143299, baseEnd_143299] using wordTrace_append hprefix tailTrace_143299
  have hstable : (prefixWord ++ tailWord_143299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143299).length < 2 ^ (prefixWord ++ tailWord_143299).sum := by decide
  have hdescent : baseEnd_143299 < baseStart_143299 := by decide
  rcases family_descends (prefixWord ++ tailWord_143299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143316 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_143316 : Nat := 118140960795 + 143316 * 2 ^ 59
def prefixEnd_143316 : Nat := 4983230072969 + 3 ^ 40 * 143316 * 2
def baseEnd_143316 : Nat := 49059995653244339460605

theorem tailTrace_143316 : CollatzResearch.WordTrace tailWord_143316 prefixEnd_143316 49059995653244339460605 := by
  unfold tailWord_143316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613581974399041634620901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3484775965865388846161201 2613581974399041634620901)
  ·
    refine ⟨490046620199820306491419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2613581974399041634620901 490046620199820306491419)
    ·
      refine ⟨735069930299730459737129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490046620199820306491419 735069930299730459737129)
      ·
        refine ⟨551302447724797844802847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 735069930299730459737129 551302447724797844802847)
        ·
          refine ⟨826953671587196767204271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551302447724797844802847 826953671587196767204271)
          ·
            refine ⟨1240430507380795150806407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826953671587196767204271 1240430507380795150806407)
            ·
              refine ⟨1860645761071192726209611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240430507380795150806407 1860645761071192726209611)
              ·
                refine ⟨2790968641606789089314417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860645761071192726209611 2790968641606789089314417)
                ·
                  refine ⟨2093226481205091816985813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2790968641606789089314417 2093226481205091816985813)
                  ·
                    refine ⟨49059995653244339460605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2093226481205091816985813 49059995653244339460605)
                    ·
                      rfl

theorem cell22_143316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_143316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143316 prefixEnd_143316 := by exact prefixLift 143316
  have htrace : WordTrace (prefixWord ++ tailWord_143316) baseStart_143316 baseEnd_143316 := by
    simpa [prefixWord, tailWord_143316, baseEnd_143316] using wordTrace_append hprefix tailTrace_143316
  have hstable : (prefixWord ++ tailWord_143316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143316).length < 2 ^ (prefixWord ++ tailWord_143316).sum := by decide
  have hdescent : baseEnd_143316 < baseStart_143316 := by decide
  rcases family_descends (prefixWord ++ tailWord_143316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143361 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_143361 : Nat := 118140960795 + 143361 * 2 ^ 59
def prefixEnd_143361 : Nat := 4983230072969 + 3 ^ 40 * 143361 * 2
def baseEnd_143361 : Nat := 49075400072879222085467

theorem tailTrace_143361 : CollatzResearch.WordTrace tailWord_143361 prefixEnd_143361 49075400072879222085467 := by
  unfold tailWord_143361
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228805233635055954629937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3485870155756703969753291 5228805233635055954629937)
  ·
    refine ⟨3921603925226291965972453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5228805233635055954629937 3921603925226291965972453)
    ·
      refine ⟨735300735979929743619835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3921603925226291965972453 735300735979929743619835)
      ·
        refine ⟨1102951103969894615429753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735300735979929743619835 1102951103969894615429753)
        ·
          refine ⟨827213327977420961572315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102951103969894615429753 827213327977420961572315)
          ·
            refine ⟨1240819991966131442358473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827213327977420961572315 1240819991966131442358473)
            ·
              refine ⟨930614993974598581768855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240819991966131442358473 930614993974598581768855)
              ·
                refine ⟨1395922490961897872653283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930614993974598581768855 1395922490961897872653283)
                ·
                  refine ⟨2093883736442846808979925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395922490961897872653283 2093883736442846808979925)
                  ·
                    refine ⟨49075400072879222085467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2093883736442846808979925 49075400072879222085467)
                    ·
                      rfl

theorem cell22_143361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_143361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143361 prefixEnd_143361 := by exact prefixLift 143361
  have htrace : WordTrace (prefixWord ++ tailWord_143361) baseStart_143361 baseEnd_143361 := by
    simpa [prefixWord, tailWord_143361, baseEnd_143361] using wordTrace_append hprefix tailTrace_143361
  have hstable : (prefixWord ++ tailWord_143361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143361).length < 2 ^ (prefixWord ++ tailWord_143361).sum := by decide
  have hdescent : baseEnd_143361 < baseStart_143361 := by decide
  rcases family_descends (prefixWord ++ tailWord_143361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143376 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_143376 : Nat := 118140960795 + 143376 * 2 ^ 59
def prefixEnd_143376 : Nat := 4983230072969 + 3 ^ 40 * 143376 * 2
def baseEnd_143376 : Nat := 49080534879424182960421

theorem tailTrace_143376 : CollatzResearch.WordTrace tailWord_143376 prefixEnd_143376 49080534879424182960421 := by
  unfold tailWord_143376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614676164290356758212991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3486234885720475677617321 2614676164290356758212991)
  ·
    refine ⟨3922014246435535137319487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2614676164290356758212991 3922014246435535137319487)
    ·
      refine ⟨5883021369653302705979231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3922014246435535137319487 5883021369653302705979231)
      ·
        refine ⟨8824532054479954058968847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883021369653302705979231 8824532054479954058968847)
        ·
          refine ⟨13236798081719931088453271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8824532054479954058968847 13236798081719931088453271)
          ·
            refine ⟨19855197122579896632679907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13236798081719931088453271 19855197122579896632679907)
            ·
              refine ⟨29782795683869844949019861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19855197122579896632679907 29782795683869844949019861)
              ·
                refine ⟨698034273840699490992653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29782795683869844949019861 698034273840699490992653)
                ·
                  refine ⟨261762852690262309122245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698034273840699490992653 261762852690262309122245)
                  ·
                    refine ⟨49080534879424182960421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261762852690262309122245 49080534879424182960421)
                    ·
                      rfl

theorem cell22_143376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_143376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143376 prefixEnd_143376 := by exact prefixLift 143376
  have htrace : WordTrace (prefixWord ++ tailWord_143376) baseStart_143376 baseEnd_143376 := by
    simpa [prefixWord, tailWord_143376, baseEnd_143376] using wordTrace_append hprefix tailTrace_143376
  have hstable : (prefixWord ++ tailWord_143376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143376).length < 2 ^ (prefixWord ++ tailWord_143376).sum := by decide
  have hdescent : baseEnd_143376 < baseStart_143376 := by decide
  rcases family_descends (prefixWord ++ tailWord_143376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143436 : List Nat := [2, 2, 1, 3, 1, 1, 2, 10]
def baseStart_143436 : Nat := 118140960795 + 143436 * 2 ^ 59
def prefixEnd_143436 : Nat := 4983230072969 + 3 ^ 40 * 143436 * 2
def baseEnd_143436 : Nat := 5455674900622669606693

theorem tailTrace_143436 : CollatzResearch.WordTrace tailWord_143436 prefixEnd_143436 5455674900622669606693 := by
  unfold tailWord_143436
  simp only [CollatzResearch.WordTrace]
  refine ⟨2615770354181671881805081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3487693805575562509073441 2615770354181671881805081)
  ·
    refine ⟨1961827765636253911353811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2615770354181671881805081 1961827765636253911353811)
    ·
      refine ⟨2942741648454380867030717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1961827765636253911353811 2942741648454380867030717)
      ·
        refine ⟨1103528118170392825136519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2942741648454380867030717 1103528118170392825136519)
        ·
          refine ⟨1655292177255589237704779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103528118170392825136519 1655292177255589237704779)
          ·
            refine ⟨2482938265883383856557169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655292177255589237704779 2482938265883383856557169)
            ·
              refine ⟨1862203699412537892417877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2482938265883383856557169 1862203699412537892417877)
              ·
                refine ⟨5455674900622669606693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1862203699412537892417877 5455674900622669606693)
                ·
                  rfl

theorem cell22_143436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 10].length) (baseStart_143436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143436 prefixEnd_143436 := by exact prefixLift 143436
  have htrace : WordTrace (prefixWord ++ tailWord_143436) baseStart_143436 baseEnd_143436 := by
    simpa [prefixWord, tailWord_143436, baseEnd_143436] using wordTrace_append hprefix tailTrace_143436
  have hstable : (prefixWord ++ tailWord_143436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143436).length < 2 ^ (prefixWord ++ tailWord_143436).sum := by decide
  have hdescent : baseEnd_143436 < baseStart_143436 := by decide
  rcases family_descends (prefixWord ++ tailWord_143436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143438 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_143438 : Nat := 118140960795 + 143438 * 2 ^ 59
def prefixEnd_143438 : Nat := 4983230072969 + 3 ^ 40 * 143438 * 2
def baseEnd_143438 : Nat := 49101758746476687910231

theorem tailTrace_143438 : CollatzResearch.WordTrace tailWord_143438 prefixEnd_143438 49101758746476687910231 := by
  unfold tailWord_143438
  simp only [CollatzResearch.WordTrace]
  refine ⟨653951706794512263147871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3487742436237398736788645 653951706794512263147871)
  ·
    refine ⟨980927560191768394721807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 653951706794512263147871 980927560191768394721807)
    ·
      refine ⟨1471391340287652592082711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980927560191768394721807 1471391340287652592082711)
      ·
        refine ⟨2207087010431478888124067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471391340287652592082711 2207087010431478888124067)
        ·
          refine ⟨3310630515647218332186101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207087010431478888124067 3310630515647218332186101)
          ·
            refine ⟨310371610841926718642447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3310630515647218332186101 310371610841926718642447)
            ·
              refine ⟨465557416262890077963671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310371610841926718642447 465557416262890077963671)
              ·
                refine ⟨698336124394335116945507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465557416262890077963671 698336124394335116945507)
                ·
                  refine ⟨1047504186591502675418261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698336124394335116945507 1047504186591502675418261)
                  ·
                    refine ⟨49101758746476687910231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1047504186591502675418261 49101758746476687910231)
                    ·
                      rfl

theorem cell22_143438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_143438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143438 prefixEnd_143438 := by exact prefixLift 143438
  have htrace : WordTrace (prefixWord ++ tailWord_143438) baseStart_143438 baseEnd_143438 := by
    simpa [prefixWord, tailWord_143438, baseEnd_143438] using wordTrace_append hprefix tailTrace_143438
  have hstable : (prefixWord ++ tailWord_143438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143438).length < 2 ^ (prefixWord ++ tailWord_143438).sum := by decide
  have hdescent : baseEnd_143438 < baseStart_143438 := by decide
  rcases family_descends (prefixWord ++ tailWord_143438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143442 : List Nat := [3, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_143442 : Nat := 118140960795 + 143442 * 2 ^ 59
def prefixEnd_143442 : Nat := 4983230072969 + 3 ^ 40 * 143442 * 2
def baseEnd_143442 : Nat := 16367709342740670270073

theorem tailTrace_143442 : CollatzResearch.WordTrace tailWord_143442 prefixEnd_143442 16367709342740670270073 := by
  unfold tailWord_143442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307939886585401697082145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3487839697561071192219053 1307939886585401697082145)
  ·
    refine ⟨980954914939051272811609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1307939886585401697082145 980954914939051272811609)
    ·
      refine ⟨735716186204288454608707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 980954914939051272811609 735716186204288454608707)
      ·
        refine ⟨1103574279306432681913061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735716186204288454608707 1103574279306432681913061)
        ·
          refine ⟨206920177369956127858699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1103574279306432681913061 206920177369956127858699)
          ·
            refine ⟨310380266054934191788049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206920177369956127858699 310380266054934191788049)
            ·
              refine ⟨232785199541200643841037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310380266054934191788049 232785199541200643841037)
              ·
                refine ⟨87294449827950241440389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232785199541200643841037 87294449827950241440389)
                ·
                  refine ⟨16367709342740670270073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87294449827950241440389 16367709342740670270073)
                  ·
                    rfl

theorem cell22_143442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_143442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143442 prefixEnd_143442 := by exact prefixLift 143442
  have htrace : WordTrace (prefixWord ++ tailWord_143442) baseStart_143442 baseEnd_143442 := by
    simpa [prefixWord, tailWord_143442, baseEnd_143442] using wordTrace_append hprefix tailTrace_143442
  have hstable : (prefixWord ++ tailWord_143442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143442).length < 2 ^ (prefixWord ++ tailWord_143442).sum := by decide
  have hdescent : baseEnd_143442 < baseStart_143442 := by decide
  rcases family_descends (prefixWord ++ tailWord_143442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143485 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_143485 : Nat := 118140960795 + 143485 * 2 ^ 59
def prefixEnd_143485 : Nat := 4983230072969 + 3 ^ 40 * 143485 * 2
def baseEnd_143485 : Nat := 49117847806984231985087

theorem tailTrace_143485 : CollatzResearch.WordTrace tailWord_143485 prefixEnd_143485 49117847806984231985087 := by
  unfold tailWord_143485
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233327885185825132143909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3488885256790550088095939 5233327885185825132143909)
  ·
    refine ⟨981248978472342212276983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5233327885185825132143909 981248978472342212276983)
    ·
      refine ⟨1471873467708513318415475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981248978472342212276983 1471873467708513318415475)
      ·
        refine ⟨2207810201562769977623213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471873467708513318415475 2207810201562769977623213)
        ·
          refine ⟨827928825586038741608705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2207810201562769977623213 827928825586038741608705)
          ·
            refine ⟨620946619189529056206529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827928825586038741608705 620946619189529056206529)
            ·
              refine ⟨465709964392146792154897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620946619189529056206529 465709964392146792154897)
              ·
                refine ⟨349282473294110094116173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465709964392146792154897 349282473294110094116173)
                ·
                  refine ⟨130980927485291285293565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349282473294110094116173 130980927485291285293565)
                  ·
                    refine ⟨49117847806984231985087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130980927485291285293565 49117847806984231985087)
                    ·
                      rfl

theorem cell22_143485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_143485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143485 prefixEnd_143485 := by exact prefixLift 143485
  have htrace : WordTrace (prefixWord ++ tailWord_143485) baseStart_143485 baseEnd_143485 := by
    simpa [prefixWord, tailWord_143485, baseEnd_143485] using wordTrace_append hprefix tailTrace_143485
  have hstable : (prefixWord ++ tailWord_143485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143485).length < 2 ^ (prefixWord ++ tailWord_143485).sum := by decide
  have hdescent : baseEnd_143485 < baseStart_143485 := by decide
  rcases family_descends (prefixWord ++ tailWord_143485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143498 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_143498 : Nat := 118140960795 + 143498 * 2 ^ 59
def prefixEnd_143498 : Nat := 4983230072969 + 3 ^ 40 * 143498 * 2
def baseEnd_143498 : Nat := 16374099324218843803349

theorem tailTrace_143498 : CollatzResearch.WordTrace tailWord_143498 prefixEnd_143498 16374099324218843803349 := by
  unfold tailWord_143498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308450508534682088091787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3489201356092485568244765 1308450508534682088091787)
  ·
    refine ⟨1962675762802023132137681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1308450508534682088091787 1962675762802023132137681)
    ·
      refine ⟨1472006822101517349103261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1962675762802023132137681 1472006822101517349103261)
      ·
        refine ⟨552002558288069005913723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1472006822101517349103261 552002558288069005913723)
        ·
          refine ⟨828003837432103508870585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552002558288069005913723 828003837432103508870585)
          ·
            refine ⟨621002878074077631652939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828003837432103508870585 621002878074077631652939)
            ·
              refine ⟨931504317111116447479409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621002878074077631652939 931504317111116447479409)
              ·
                refine ⟨698628237833337335609557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931504317111116447479409 698628237833337335609557)
                ·
                  refine ⟨16374099324218843803349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 698628237833337335609557 16374099324218843803349)
                  ·
                    rfl

theorem cell22_143498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_143498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143498 prefixEnd_143498 := by exact prefixLift 143498
  have htrace : WordTrace (prefixWord ++ tailWord_143498) baseStart_143498 baseEnd_143498 := by
    simpa [prefixWord, tailWord_143498, baseEnd_143498] using wordTrace_append hprefix tailTrace_143498
  have hstable : (prefixWord ++ tailWord_143498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143498).length < 2 ^ (prefixWord ++ tailWord_143498).sum := by decide
  have hdescent : baseEnd_143498 < baseStart_143498 := by decide
  rcases family_descends (prefixWord ++ tailWord_143498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143510 : List Nat := [5, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_143510 : Nat := 118140960795 + 143510 * 2 ^ 59
def prefixEnd_143510 : Nat := 4983230072969 + 3 ^ 40 * 143510 * 2
def baseEnd_143510 : Nat := 16375468605964166703337

theorem tailTrace_143510 : CollatzResearch.WordTrace tailWord_143510 prefixEnd_143510 16375468605964166703337 := by
  unfold tailWord_143510
  simp only [CollatzResearch.WordTrace]
  refine ⟨327139981880953400112749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3489493140063502934535989 327139981880953400112749)
  ·
    refine ⟨122677493205357525042281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 327139981880953400112749 122677493205357525042281)
    ·
      refine ⟨92008119904018143781711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122677493205357525042281 92008119904018143781711)
      ·
        refine ⟨138012179856027215672567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92008119904018143781711 138012179856027215672567)
        ·
          refine ⟨207018269784040823508851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138012179856027215672567 207018269784040823508851)
          ·
            refine ⟨310527404676061235263277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207018269784040823508851 310527404676061235263277)
            ·
              refine ⟨116447776753522963223729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 310527404676061235263277 116447776753522963223729)
              ·
                refine ⟨87335832565142222417797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116447776753522963223729 87335832565142222417797)
                ·
                  refine ⟨16375468605964166703337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87335832565142222417797 16375468605964166703337)
                  ·
                    rfl

theorem cell22_143510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_143510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143510 prefixEnd_143510 := by exact prefixLift 143510
  have htrace : WordTrace (prefixWord ++ tailWord_143510) baseStart_143510 baseEnd_143510 := by
    simpa [prefixWord, tailWord_143510, baseEnd_143510] using wordTrace_append hprefix tailTrace_143510
  have hstable : (prefixWord ++ tailWord_143510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143510).length < 2 ^ (prefixWord ++ tailWord_143510).sum := by decide
  have hdescent : baseEnd_143510 < baseStart_143510 := by decide
  rcases family_descends (prefixWord ++ tailWord_143510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143560 : List Nat := [2, 1, 3, 1, 2, 1, 1, 7, 4]
def baseStart_143560 : Nat := 118140960795 + 143560 * 2 ^ 59
def prefixEnd_143560 : Nat := 4983230072969 + 3 ^ 40 * 143560 * 2
def baseEnd_143560 : Nat := 16381173946569678786619

theorem tailTrace_143560 : CollatzResearch.WordTrace tailWord_143560 prefixEnd_143560 16381173946569678786619 := by
  unfold tailWord_143560
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618031679957056470562067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3490708906609408627416089 2618031679957056470562067)
  ·
    refine ⟨3927047519935584705843101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2618031679957056470562067 3927047519935584705843101)
    ·
      refine ⟨1472642819975844264691163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3927047519935584705843101 1472642819975844264691163)
      ·
        refine ⟨2208964229963766397036745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472642819975844264691163 2208964229963766397036745)
        ·
          refine ⟨1656723172472824797777559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2208964229963766397036745 1656723172472824797777559)
          ·
            refine ⟨2485084758709237196666339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656723172472824797777559 2485084758709237196666339)
            ·
              refine ⟨3727627138063855794999509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485084758709237196666339 3727627138063855794999509)
              ·
                refine ⟨87366261048371620195301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3727627138063855794999509 87366261048371620195301)
                ·
                  refine ⟨16381173946569678786619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87366261048371620195301 16381173946569678786619)
                  ·
                    rfl

theorem cell22_143560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_143560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143560 prefixEnd_143560 := by exact prefixLift 143560
  have htrace : WordTrace (prefixWord ++ tailWord_143560) baseStart_143560 baseEnd_143560 := by
    simpa [prefixWord, tailWord_143560, baseEnd_143560] using wordTrace_append hprefix tailTrace_143560
  have hstable : (prefixWord ++ tailWord_143560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143560).length < 2 ^ (prefixWord ++ tailWord_143560).sum := by decide
  have hdescent : baseEnd_143560 < baseStart_143560 := by decide
  rcases family_descends (prefixWord ++ tailWord_143560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143562 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_143562 : Nat := 118140960795 + 143562 * 2 ^ 59
def prefixEnd_143562 : Nat := 4983230072969 + 3 ^ 40 * 143562 * 2
def baseEnd_143562 : Nat := 49144206480581697809851

theorem tailTrace_143562 : CollatzResearch.WordTrace tailWord_143562 prefixEnd_143562 49144206480581697809851 := by
  unfold tailWord_143562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309034076476716820674235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3490757537271244855131293 1309034076476716820674235)
  ·
    refine ⟨1963551114715075231011353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1309034076476716820674235 1963551114715075231011353)
    ·
      refine ⟨1472663336036306423258515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1963551114715075231011353 1472663336036306423258515)
      ·
        refine ⟨2208995004054459634887773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472663336036306423258515 2208995004054459634887773)
        ·
          refine ⟨828373126520422363082915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2208995004054459634887773 828373126520422363082915)
          ·
            refine ⟨1242559689780633544624373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828373126520422363082915 1242559689780633544624373)
            ·
              refine ⟨116489970916934394808535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1242559689780633544624373 116489970916934394808535)
              ·
                refine ⟨174734956375401592212803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116489970916934394808535 174734956375401592212803)
                ·
                  refine ⟨262102434563102388319205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174734956375401592212803 262102434563102388319205)
                  ·
                    refine ⟨49144206480581697809851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262102434563102388319205 49144206480581697809851)
                    ·
                      rfl

theorem cell22_143562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_143562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143562 prefixEnd_143562 := by exact prefixLift 143562
  have htrace : WordTrace (prefixWord ++ tailWord_143562) baseStart_143562 baseEnd_143562 := by
    simpa [prefixWord, tailWord_143562, baseEnd_143562] using wordTrace_append hprefix tailTrace_143562
  have hstable : (prefixWord ++ tailWord_143562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143562).length < 2 ^ (prefixWord ++ tailWord_143562).sum := by decide
  have hdescent : baseEnd_143562 < baseStart_143562 := by decide
  rcases family_descends (prefixWord ++ tailWord_143562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143577 : List Nat := [1, 2, 1, 2, 3, 1, 6, 2, 4]
def baseStart_143577 : Nat := 118140960795 + 143577 * 2 ^ 59
def prefixEnd_143577 : Nat := 4983230072969 + 3 ^ 40 * 143577 * 2
def baseEnd_143577 : Nat := 16383113762375552894935

theorem tailTrace_143577 : CollatzResearch.WordTrace tailWord_143577 prefixEnd_143577 16383113762375552894935 := by
  unfold tailWord_143577
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236683400852524844492985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3491122267235016562995323 5236683400852524844492985)
  ·
    refine ⟨3927512550639393633369739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5236683400852524844492985 3927512550639393633369739)
    ·
      refine ⟨5891268825959090450054609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3927512550639393633369739 5891268825959090450054609)
      ·
        refine ⟨4418451619469317837540957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5891268825959090450054609 4418451619469317837540957)
        ·
          refine ⟨1656919357300994189077859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4418451619469317837540957 1656919357300994189077859)
          ·
            refine ⟨2485379035951491283616789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656919357300994189077859 2485379035951491283616789)
            ·
              refine ⟨116502142310226153919537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2485379035951491283616789 116502142310226153919537)
              ·
                refine ⟨87376606732669615439653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116502142310226153919537 87376606732669615439653)
                ·
                  refine ⟨16383113762375552894935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87376606732669615439653 16383113762375552894935)
                  ·
                    rfl

theorem cell22_143577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_143577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143577 prefixEnd_143577 := by exact prefixLift 143577
  have htrace : WordTrace (prefixWord ++ tailWord_143577) baseStart_143577 baseEnd_143577 := by
    simpa [prefixWord, tailWord_143577, baseEnd_143577] using wordTrace_append hprefix tailTrace_143577
  have hstable : (prefixWord ++ tailWord_143577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143577).length < 2 ^ (prefixWord ++ tailWord_143577).sum := by decide
  have hdescent : baseEnd_143577 < baseStart_143577 := by decide
  rcases family_descends (prefixWord ++ tailWord_143577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143592 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 2, 3]
def baseStart_143592 : Nat := 118140960795 + 143592 * 2 ^ 59
def prefixEnd_143592 : Nat := 4983230072969 + 3 ^ 40 * 143592 * 2
def baseEnd_143592 : Nat := 49154476093671619559759

theorem tailTrace_143592 : CollatzResearch.WordTrace tailWord_143592 prefixEnd_143592 49154476093671619559759 := by
  unfold tailWord_143592
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618615247899091203144515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3491486997198788270859353 2618615247899091203144515)
  ·
    refine ⟨3927922871848636804716773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2618615247899091203144515 3927922871848636804716773)
    ·
      refine ⟨736485538471619400884395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3927922871848636804716773 736485538471619400884395)
      ·
        refine ⟨1104728307707429101326593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736485538471619400884395 1104728307707429101326593)
        ·
          refine ⟨828546230780571825994945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104728307707429101326593 828546230780571825994945)
          ·
            refine ⟨621409673085428869496209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828546230780571825994945 621409673085428869496209)
            ·
              refine ⟨466057254814071652122157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621409673085428869496209 466057254814071652122157)
              ·
                refine ⟨174771470555276869545809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466057254814071652122157 174771470555276869545809)
                ·
                  refine ⟨131078602916457652159357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174771470555276869545809 131078602916457652159357)
                  ·
                    refine ⟨49154476093671619559759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131078602916457652159357 49154476093671619559759)
                    ·
                      rfl

theorem cell22_143592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_143592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143592 prefixEnd_143592 := by exact prefixLift 143592
  have htrace : WordTrace (prefixWord ++ tailWord_143592) baseStart_143592 baseEnd_143592 := by
    simpa [prefixWord, tailWord_143592, baseEnd_143592] using wordTrace_append hprefix tailTrace_143592
  have hstable : (prefixWord ++ tailWord_143592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143592).length < 2 ^ (prefixWord ++ tailWord_143592).sum := by decide
  have hdescent : baseEnd_143592 < baseStart_143592 := by decide
  rcases family_descends (prefixWord ++ tailWord_143592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143701 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 5]
def baseStart_143701 : Nat := 118140960795 + 143701 * 2 ^ 59
def prefixEnd_143701 : Nat := 4983230072969 + 3 ^ 40 * 143701 * 2
def baseEnd_143701 : Nat := 16397263007077222861475

theorem tailTrace_143701 : CollatzResearch.WordTrace tailWord_143701 prefixEnd_143701 16397263007077222861475 := by
  unfold tailWord_143701
  simp only [CollatzResearch.WordTrace]
  refine ⟨5241206052403294022006957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3494137368268862681337971 5241206052403294022006957)
  ·
    refine ⟨1965452269651235258252609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5241206052403294022006957 1965452269651235258252609)
    ·
      refine ⟨1474089202238426443689457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1965452269651235258252609 1474089202238426443689457)
      ·
        refine ⟨1105566901678819832767093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1474089202238426443689457 1105566901678819832767093)
        ·
          refine ⟨103646897032389359321915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1105566901678819832767093 103646897032389359321915)
          ·
            refine ⟨155470345548584038982873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103646897032389359321915 155470345548584038982873)
            ·
              refine ⟨116602759161438029237155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155470345548584038982873 116602759161438029237155)
              ·
                refine ⟨174904138742157043855733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116602759161438029237155 174904138742157043855733)
                ·
                  refine ⟨16397263007077222861475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174904138742157043855733 16397263007077222861475)
                  ·
                    rfl

theorem cell22_143701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_143701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143701 prefixEnd_143701 := by exact prefixLift 143701
  have htrace : WordTrace (prefixWord ++ tailWord_143701) baseStart_143701 baseEnd_143701 := by
    simpa [prefixWord, tailWord_143701, baseEnd_143701] using wordTrace_append hprefix tailTrace_143701
  have hstable : (prefixWord ++ tailWord_143701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143701).length < 2 ^ (prefixWord ++ tailWord_143701).sum := by decide
  have hdescent : baseEnd_143701 < baseStart_143701 := by decide
  rcases family_descends (prefixWord ++ tailWord_143701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143714 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_143714 : Nat := 118140960795 + 143714 * 2 ^ 59
def prefixEnd_143714 : Nat := 4983230072969 + 3 ^ 40 * 143714 * 2
def baseEnd_143714 : Nat := 49196239186903968009385

theorem tailTrace_143714 : CollatzResearch.WordTrace tailWord_143714 prefixEnd_143714 49196239186903968009385 := by
  unfold tailWord_143714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310420050339049310557549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3494453467570798161486797 1310420050339049310557549)
  ·
    refine ⟨491407518877143491459081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1310420050339049310557549 491407518877143491459081)
    ·
      refine ⟨368555639157857618594311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 491407518877143491459081 368555639157857618594311)
      ·
        refine ⟨552833458736786427891467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368555639157857618594311 552833458736786427891467)
        ·
          refine ⟨829250188105179641837201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552833458736786427891467 829250188105179641837201)
          ·
            refine ⟨621937641078884731377901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829250188105179641837201 621937641078884731377901)
            ·
              refine ⟨233226615404581774266713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 621937641078884731377901 233226615404581774266713)
              ·
                refine ⟨174919961553436330700035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233226615404581774266713 174919961553436330700035)
                ·
                  refine ⟨262379942330154496050053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174919961553436330700035 262379942330154496050053)
                  ·
                    refine ⟨49196239186903968009385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262379942330154496050053 49196239186903968009385)
                    ·
                      rfl

theorem cell22_143714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_143714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143714 prefixEnd_143714 := by exact prefixLift 143714
  have htrace : WordTrace (prefixWord ++ tailWord_143714) baseStart_143714 baseEnd_143714 := by
    simpa [prefixWord, tailWord_143714, baseEnd_143714] using wordTrace_append hprefix tailTrace_143714
  have hstable : (prefixWord ++ tailWord_143714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143714).length < 2 ^ (prefixWord ++ tailWord_143714).sum := by decide
  have hdescent : baseEnd_143714 < baseStart_143714 := by decide
  rcases family_descends (prefixWord ++ tailWord_143714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143806 : List Nat := [4, 2, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_143806 : Nat := 118140960795 + 143806 * 2 ^ 59
def prefixEnd_143806 : Nat := 4983230072969 + 3 ^ 40 * 143806 * 2
def baseEnd_143806 : Nat := 49227732667046394709103

theorem tailTrace_143806 : CollatzResearch.WordTrace tailWord_143806 prefixEnd_143806 49227732667046394709103 := by
  unfold tailWord_143806
  simp only [CollatzResearch.WordTrace]
  refine ⟨655629464627862119322409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3496690478015264636386181 655629464627862119322409)
  ·
    refine ⟨491722098470896589491807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 655629464627862119322409 491722098470896589491807)
    ·
      refine ⟨737583147706344884237711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491722098470896589491807 737583147706344884237711)
      ·
        refine ⟨1106374721559517326356567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737583147706344884237711 1106374721559517326356567)
        ·
          refine ⟨1659562082339275989534851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106374721559517326356567 1659562082339275989534851)
          ·
            refine ⟨2489343123508913984302277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659562082339275989534851 2489343123508913984302277)
            ·
              refine ⟨466751835657921372056677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2489343123508913984302277 466751835657921372056677)
              ·
                refine ⟨87515969185860257260627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466751835657921372056677 87515969185860257260627)
                ·
                  refine ⟨131273953778790385890941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87515969185860257260627 131273953778790385890941)
                  ·
                    refine ⟨49227732667046394709103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131273953778790385890941 49227732667046394709103)
                    ·
                      rfl

theorem cell22_143806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_143806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143806 prefixEnd_143806 := by exact prefixLift 143806
  have htrace : WordTrace (prefixWord ++ tailWord_143806) baseStart_143806 baseEnd_143806 := by
    simpa [prefixWord, tailWord_143806, baseEnd_143806] using wordTrace_append hprefix tailTrace_143806
  have hstable : (prefixWord ++ tailWord_143806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143806).length < 2 ^ (prefixWord ++ tailWord_143806).sum := by decide
  have hdescent : baseEnd_143806 < baseStart_143806 := by decide
  rcases family_descends (prefixWord ++ tailWord_143806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143922 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_143922 : Nat := 118140960795 + 143922 * 2 ^ 59
def prefixEnd_143922 : Nat := 4983230072969 + 3 ^ 40 * 143922 * 2
def baseEnd_143922 : Nat := 49267441837660758808747

theorem tailTrace_143922 : CollatzResearch.WordTrace tailWord_143922 prefixEnd_143922 49267441837660758808747 := by
  unfold tailWord_143922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312316646150662191450505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3499511056401765843868013 1312316646150662191450505)
  ·
    refine ⟨984237484612996643587879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1312316646150662191450505 984237484612996643587879)
    ·
      refine ⟨1476356226919494965381819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984237484612996643587879 1476356226919494965381819)
      ·
        refine ⟨2214534340379242448072729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476356226919494965381819 2214534340379242448072729)
        ·
          refine ⟨1660900755284431836054547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2214534340379242448072729 1660900755284431836054547)
          ·
            refine ⟨2491351132926647754081821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660900755284431836054547 2491351132926647754081821)
            ·
              refine ⟨934256674847492907780683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2491351132926647754081821 934256674847492907780683)
              ·
                refine ⟨1401385012271239361671025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934256674847492907780683 1401385012271239361671025)
                ·
                  refine ⟨1051038759203429521253269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1401385012271239361671025 1051038759203429521253269)
                  ·
                    refine ⟨49267441837660758808747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1051038759203429521253269 49267441837660758808747)
                    ·
                      rfl

theorem cell22_143922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_143922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143922 prefixEnd_143922 := by exact prefixLift 143922
  have htrace : WordTrace (prefixWord ++ tailWord_143922) baseStart_143922 baseEnd_143922 := by
    simpa [prefixWord, tailWord_143922, baseEnd_143922] using wordTrace_append hprefix tailTrace_143922
  have hstable : (prefixWord ++ tailWord_143922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143922).length < 2 ^ (prefixWord ++ tailWord_143922).sum := by decide
  have hdescent : baseEnd_143922 < baseStart_143922 := by decide
  rcases family_descends (prefixWord ++ tailWord_143922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143926 : List Nat := [5, 1, 2, 1, 2, 3, 1, 7]
def baseStart_143926 : Nat := 118140960795 + 143926 * 2 ^ 59
def prefixEnd_143926 : Nat := 4983230072969 + 3 ^ 40 * 143926 * 2
def baseEnd_143926 : Nat := 5474312346600675745415

theorem tailTrace_143926 : CollatzResearch.WordTrace tailWord_143926 prefixEnd_143926 5474312346600675745415 := by
  unfold tailWord_143926
  simp only [CollatzResearch.WordTrace]
  refine ⟨328088279786759840559227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3499608317725438299298421 328088279786759840559227)
  ·
    refine ⟨492132419680139760838841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328088279786759840559227 492132419680139760838841)
    ·
      refine ⟨369099314760104820629131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 492132419680139760838841 369099314760104820629131)
      ·
        refine ⟨553648972140157230943697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369099314760104820629131 553648972140157230943697)
        ·
          refine ⟨415236729105117923207773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553648972140157230943697 415236729105117923207773)
          ·
            refine ⟨155713773414419221202915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 415236729105117923207773 155713773414419221202915)
            ·
              refine ⟨233570660121628831804373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155713773414419221202915 233570660121628831804373)
              ·
                refine ⟨5474312346600675745415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 233570660121628831804373 5474312346600675745415)
                ·
                  rfl

theorem cell22_143926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_143926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_143926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_143926 prefixEnd_143926 := by exact prefixLift 143926
  have htrace : WordTrace (prefixWord ++ tailWord_143926) baseStart_143926 baseEnd_143926 := by
    simpa [prefixWord, tailWord_143926, baseEnd_143926] using wordTrace_append hprefix tailTrace_143926
  have hstable : (prefixWord ++ tailWord_143926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143926).length < 2 ^ (prefixWord ++ tailWord_143926).sum := by decide
  have hdescent : baseEnd_143926 < baseStart_143926 := by decide
  rcases family_descends (prefixWord ++ tailWord_143926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144001 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_144001 : Nat := 118140960795 + 144001 * 2 ^ 59
def prefixEnd_144001 : Nat := 4983230072969 + 3 ^ 40 * 144001 * 2
def baseEnd_144001 : Nat := 49294485152130886083505

theorem tailTrace_144001 : CollatzResearch.WordTrace tailWord_144001 prefixEnd_144001 49294485152130886083505 := by
  unfold tailWord_144001
  simp only [CollatzResearch.WordTrace]
  refine ⟨5252147951316445257927857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3501431967544296838618571 5252147951316445257927857)
  ·
    refine ⟨3939110963487333943445893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5252147951316445257927857 3939110963487333943445893)
    ·
      refine ⟨738583305653875114396105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3939110963487333943445893 738583305653875114396105)
      ·
        refine ⟨553937479240406335797079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738583305653875114396105 553937479240406335797079)
        ·
          refine ⟨830906218860609503695619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553937479240406335797079 830906218860609503695619)
          ·
            refine ⟨1246359328290914255543429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830906218860609503695619 1246359328290914255543429)
            ·
              refine ⟨233692374054546422914393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1246359328290914255543429 233692374054546422914393)
              ·
                refine ⟨175269280540909817185795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233692374054546422914393 175269280540909817185795)
                ·
                  refine ⟨262903920811364725778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175269280540909817185795 262903920811364725778693)
                  ·
                    refine ⟨49294485152130886083505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262903920811364725778693 49294485152130886083505)
                    ·
                      rfl

theorem cell22_144001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_144001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144001 prefixEnd_144001 := by exact prefixLift 144001
  have htrace : WordTrace (prefixWord ++ tailWord_144001) baseStart_144001 baseEnd_144001 := by
    simpa [prefixWord, tailWord_144001, baseEnd_144001] using wordTrace_append hprefix tailTrace_144001
  have hstable : (prefixWord ++ tailWord_144001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144001).length < 2 ^ (prefixWord ++ tailWord_144001).sum := by decide
  have hdescent : baseEnd_144001 < baseStart_144001 := by decide
  rcases family_descends (prefixWord ++ tailWord_144001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144014 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_144014 : Nat := 118140960795 + 144014 * 2 ^ 59
def prefixEnd_144014 : Nat := 4983230072969 + 3 ^ 40 * 144014 * 2
def baseEnd_144014 : Nat := 49298935317803185508465

theorem tailTrace_144014 : CollatzResearch.WordTrace tailWord_144014 prefixEnd_144014 49298935317803185508465 := by
  unfold tailWord_144014
  simp only [CollatzResearch.WordTrace]
  refine ⟨656577762533668559768887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3501748066846232318767397 656577762533668559768887)
  ·
    refine ⟨984866643800502839653331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 656577762533668559768887 984866643800502839653331)
    ·
      refine ⟨1477299965700754259479997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984866643800502839653331 1477299965700754259479997)
      ·
        refine ⟨553987487137782847304999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1477299965700754259479997 553987487137782847304999)
        ·
          refine ⟨830981230706674270957499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553987487137782847304999 830981230706674270957499)
          ·
            refine ⟨1246471846060011406436249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830981230706674270957499 1246471846060011406436249)
            ·
              refine ⟨934853884545008554827187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246471846060011406436249 934853884545008554827187)
              ·
                refine ⟨1402280826817512832240781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934853884545008554827187 1402280826817512832240781)
                ·
                  refine ⟨525855310056567312090293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1402280826817512832240781 525855310056567312090293)
                  ·
                    refine ⟨49298935317803185508465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 525855310056567312090293 49298935317803185508465)
                    ·
                      rfl

theorem cell22_144014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_144014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144014 prefixEnd_144014 := by exact prefixLift 144014
  have htrace : WordTrace (prefixWord ++ tailWord_144014) baseStart_144014 baseEnd_144014 := by
    simpa [prefixWord, tailWord_144014, baseEnd_144014] using wordTrace_append hprefix tailTrace_144014
  have hstable : (prefixWord ++ tailWord_144014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144014).length < 2 ^ (prefixWord ++ tailWord_144014).sum := by decide
  have hdescent : baseEnd_144014 < baseStart_144014 := by decide
  rcases family_descends (prefixWord ++ tailWord_144014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144029 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_144029 : Nat := 118140960795 + 144029 * 2 ^ 59
def prefixEnd_144029 : Nat := 4983230072969 + 3 ^ 40 * 144029 * 2
def baseEnd_144029 : Nat := 49304070124348146383419

theorem tailTrace_144029 : CollatzResearch.WordTrace tailWord_144029 prefixEnd_144029 49304070124348146383419 := by
  unfold tailWord_144029
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253169195215006039947141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3502112796810004026631427 5253169195215006039947141)
  ·
    refine ⟨984969224102813632490089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5253169195215006039947141 984969224102813632490089)
    ·
      refine ⟨738726918077110224367567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 984969224102813632490089 738726918077110224367567)
      ·
        refine ⟨1108090377115665336551351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738726918077110224367567 1108090377115665336551351)
        ·
          refine ⟨1662135565673498004827027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108090377115665336551351 1662135565673498004827027)
          ·
            refine ⟨2493203348510247007240541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662135565673498004827027 2493203348510247007240541)
            ·
              refine ⟨934951255691342627715203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2493203348510247007240541 934951255691342627715203)
              ·
                refine ⟨1402426883537013941572805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934951255691342627715203 1402426883537013941572805)
                ·
                  refine ⟨262955040663190114044901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402426883537013941572805 262955040663190114044901)
                  ·
                    refine ⟨49304070124348146383419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262955040663190114044901 49304070124348146383419)
                    ·
                      rfl

theorem cell22_144029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_144029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144029 prefixEnd_144029 := by exact prefixLift 144029
  have htrace : WordTrace (prefixWord ++ tailWord_144029) baseStart_144029 baseEnd_144029 := by
    simpa [prefixWord, tailWord_144029, baseEnd_144029] using wordTrace_append hprefix tailTrace_144029
  have hstable : (prefixWord ++ tailWord_144029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144029).length < 2 ^ (prefixWord ++ tailWord_144029).sum := by decide
  have hdescent : baseEnd_144029 < baseStart_144029 := by decide
  rcases family_descends (prefixWord ++ tailWord_144029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144033 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 6]
def baseStart_144033 : Nat := 118140960795 + 144033 * 2 ^ 59
def prefixEnd_144033 : Nat := 4983230072969 + 3 ^ 40 * 144033 * 2
def baseEnd_144033 : Nat := 16435146468697823094469

theorem tailTrace_144033 : CollatzResearch.WordTrace tailWord_144033 prefixEnd_144033 16435146468697823094469 := by
  unfold tailWord_144033
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253315087200514723092753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3502210058133676482061835 5253315087200514723092753)
  ·
    refine ⟨3939986315400386042319565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5253315087200514723092753 3939986315400386042319565)
    ·
      refine ⟨1477494868275144765869837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3939986315400386042319565 1477494868275144765869837)
      ·
        refine ⟨554060575603179287201189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1477494868275144765869837 554060575603179287201189)
        ·
          refine ⟨103886357925596116350223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 554060575603179287201189 103886357925596116350223)
          ·
            refine ⟨155829536888394174525335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103886357925596116350223 155829536888394174525335)
            ·
              refine ⟨233744305332591261788003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155829536888394174525335 233744305332591261788003)
              ·
                refine ⟨350616457998886892682005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233744305332591261788003 350616457998886892682005)
                ·
                  refine ⟨16435146468697823094469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 350616457998886892682005 16435146468697823094469)
                  ·
                    rfl

theorem cell22_144033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_144033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144033 prefixEnd_144033 := by exact prefixLift 144033
  have htrace : WordTrace (prefixWord ++ tailWord_144033) baseStart_144033 baseEnd_144033 := by
    simpa [prefixWord, tailWord_144033, baseEnd_144033] using wordTrace_append hprefix tailTrace_144033
  have hstable : (prefixWord ++ tailWord_144033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144033).length < 2 ^ (prefixWord ++ tailWord_144033).sum := by decide
  have hdescent : baseEnd_144033 < baseStart_144033 := by decide
  rcases family_descends (prefixWord ++ tailWord_144033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144181 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_144181 : Nat := 118140960795 + 144181 * 2 ^ 59
def prefixEnd_144181 : Nat := 4983230072969 + 3 ^ 40 * 144181 * 2
def baseEnd_144181 : Nat := 49356102830670416582953

theorem tailTrace_144181 : CollatzResearch.WordTrace tailWord_144181 prefixEnd_144181 49356102830670416582953 := by
  unfold tailWord_144181
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258713090664335999480397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3505808727109557332986931 5258713090664335999480397)
  ·
    refine ⟨1972017408999125999805149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5258713090664335999480397 1972017408999125999805149)
    ·
      refine ⟨739506528374672249926931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1972017408999125999805149 739506528374672249926931)
      ·
        refine ⟨1109259792562008374890397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739506528374672249926931 1109259792562008374890397)
        ·
          refine ⟨415972422210753140583899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1109259792562008374890397 415972422210753140583899)
          ·
            refine ⟨623958633316129710875849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415972422210753140583899 623958633316129710875849)
            ·
              refine ⟨467968974987097283156887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623958633316129710875849 467968974987097283156887)
              ·
                refine ⟨701953462480645924735331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467968974987097283156887 701953462480645924735331)
                ·
                  refine ⟨1052930193720968887102997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701953462480645924735331 1052930193720968887102997)
                  ·
                    refine ⟨49356102830670416582953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1052930193720968887102997 49356102830670416582953)
                    ·
                      rfl

theorem cell22_144181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_144181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144181 prefixEnd_144181 := by exact prefixLift 144181
  have htrace : WordTrace (prefixWord ++ tailWord_144181) baseStart_144181 baseEnd_144181 := by
    simpa [prefixWord, tailWord_144181, baseEnd_144181] using wordTrace_append hprefix tailTrace_144181
  have hstable : (prefixWord ++ tailWord_144181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144181).length < 2 ^ (prefixWord ++ tailWord_144181).sum := by decide
  have hdescent : baseEnd_144181 < baseStart_144181 := by decide
  rcases family_descends (prefixWord ++ tailWord_144181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144305 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_144305 : Nat := 118140960795 + 144305 * 2 ^ 59
def prefixEnd_144305 : Nat := 4983230072969 + 3 ^ 40 * 144305 * 2
def baseEnd_144305 : Nat := 49398550564775426482573

theorem tailTrace_144305 : CollatzResearch.WordTrace tailWord_144305 prefixEnd_144305 49398550564775426482573 := by
  unfold tailWord_144305
  simp only [CollatzResearch.WordTrace]
  refine ⟨5263235742215105176994369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3508823828143403451329579 5263235742215105176994369)
  ·
    refine ⟨3947426806661328882745777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5263235742215105176994369 3947426806661328882745777)
    ·
      refine ⟨2960570104995996662059333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3947426806661328882745777 2960570104995996662059333)
      ·
        refine ⟨555106894686749374136125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2960570104995996662059333 555106894686749374136125)
        ·
          refine ⟨208165085507531015301047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 555106894686749374136125 208165085507531015301047)
          ·
            refine ⟨312247628261296522951571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208165085507531015301047 312247628261296522951571)
            ·
              refine ⟨468371442391944784427357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312247628261296522951571 468371442391944784427357)
              ·
                refine ⟨175639290896979294160259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 468371442391944784427357 175639290896979294160259)
                ·
                  refine ⟨263458936345468941240389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175639290896979294160259 263458936345468941240389)
                  ·
                    refine ⟨49398550564775426482573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 263458936345468941240389 49398550564775426482573)
                    ·
                      rfl

theorem cell22_144305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_144305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144305 prefixEnd_144305 := by exact prefixLift 144305
  have htrace : WordTrace (prefixWord ++ tailWord_144305) baseStart_144305 baseEnd_144305 := by
    simpa [prefixWord, tailWord_144305, baseEnd_144305] using wordTrace_append hprefix tailTrace_144305
  have hstable : (prefixWord ++ tailWord_144305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144305).length < 2 ^ (prefixWord ++ tailWord_144305).sum := by decide
  have hdescent : baseEnd_144305 < baseStart_144305 := by decide
  rcases family_descends (prefixWord ++ tailWord_144305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144354 : List Nat := [3, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_144354 : Nat := 118140960795 + 144354 * 2 ^ 59
def prefixEnd_144354 : Nat := 4983230072969 + 3 ^ 40 * 144354 * 2
def baseEnd_144354 : Nat := 16471774755385210669141

theorem tailTrace_144354 : CollatzResearch.WordTrace tailWord_144354 prefixEnd_144354 16471774755385210669141 := by
  unfold tailWord_144354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316255729759396636382029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3510015279358391030352077 1316255729759396636382029)
  ·
    refine ⟨493595898659773738643261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1316255729759396636382029 493595898659773738643261)
    ·
      refine ⟨185098461997415151991223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 493595898659773738643261 185098461997415151991223)
      ·
        refine ⟨277647692996122727986835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185098461997415151991223 277647692996122727986835)
        ·
          refine ⟨416471539494184091980253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277647692996122727986835 416471539494184091980253)
          ·
            refine ⟨156176827310319034492595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 416471539494184091980253 156176827310319034492595)
            ·
              refine ⟨234265240965478551738893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156176827310319034492595 234265240965478551738893)
              ·
                refine ⟨87849465362054456902085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234265240965478551738893 87849465362054456902085)
                ·
                  refine ⟨16471774755385210669141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87849465362054456902085 16471774755385210669141)
                  ·
                    rfl

theorem cell22_144354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_144354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144354 prefixEnd_144354 := by exact prefixLift 144354
  have htrace : WordTrace (prefixWord ++ tailWord_144354) baseStart_144354 baseEnd_144354 := by
    simpa [prefixWord, tailWord_144354, baseEnd_144354] using wordTrace_append hprefix tailTrace_144354
  have hstable : (prefixWord ++ tailWord_144354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144354).length < 2 ^ (prefixWord ++ tailWord_144354).sum := by decide
  have hdescent : baseEnd_144354 < baseStart_144354 := by decide
  rcases family_descends (prefixWord ++ tailWord_144354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144380 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_144380 : Nat := 118140960795 + 144380 * 2 ^ 59
def prefixEnd_144380 : Nat := 4983230072969 + 3 ^ 40 * 144380 * 2
def baseEnd_144380 : Nat := 49424224597500230857343

theorem tailTrace_144380 : CollatzResearch.WordTrace tailWord_144380 prefixEnd_144380 49424224597500230857343 := by
  unfold tailWord_144380
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632985608471696492987297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3510647477962261990649729 2632985608471696492987297)
  ·
    refine ⟨1974739206353772369740473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2632985608471696492987297 1974739206353772369740473)
    ·
      refine ⟨1481054404765329277305355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1974739206353772369740473 1481054404765329277305355)
      ·
        refine ⟨2221581607147993915958033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481054404765329277305355 2221581607147993915958033)
        ·
          refine ⟨1666186205360995436968525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221581607147993915958033 1666186205360995436968525)
          ·
            refine ⟨624819827010373288863197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1666186205360995436968525 624819827010373288863197)
            ·
              refine ⟨234307435128889983323699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 624819827010373288863197 234307435128889983323699)
              ·
                refine ⟨351461152693334974985549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234307435128889983323699 351461152693334974985549)
                ·
                  refine ⟨131797932260000615619581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351461152693334974985549 131797932260000615619581)
                  ·
                    refine ⟨49424224597500230857343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131797932260000615619581 49424224597500230857343)
                    ·
                      rfl

theorem cell22_144380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_144380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144380 prefixEnd_144380 := by exact prefixLift 144380
  have htrace : WordTrace (prefixWord ++ tailWord_144380) baseStart_144380 baseEnd_144380 := by
    simpa [prefixWord, tailWord_144380, baseEnd_144380] using wordTrace_append hprefix tailTrace_144380
  have hstable : (prefixWord ++ tailWord_144380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144380).length < 2 ^ (prefixWord ++ tailWord_144380).sum := by decide
  have hdescent : baseEnd_144380 < baseStart_144380 := by decide
  rcases family_descends (prefixWord ++ tailWord_144380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144453 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_144453 : Nat := 118140960795 + 144453 * 2 ^ 59
def prefixEnd_144453 : Nat := 4983230072969 + 3 ^ 40 * 144453 * 2
def baseEnd_144453 : Nat := 49449213989352373782119

theorem tailTrace_144453 : CollatzResearch.WordTrace tailWord_144453 prefixEnd_144453 49449213989352373782119 := by
  unfold tailWord_144453
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268633745678926453382013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3512422497119284302254675 5268633745678926453382013)
  ·
    refine ⟨1975737654629597420018255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5268633745678926453382013 1975737654629597420018255)
    ·
      refine ⟨2963606481944396130027383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975737654629597420018255 2963606481944396130027383)
      ·
        refine ⟨4445409722916594195041075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963606481944396130027383 4445409722916594195041075)
        ·
          refine ⟨6668114584374891292561613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445409722916594195041075 6668114584374891292561613)
          ·
            refine ⟨2500542969140584234710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6668114584374891292561613 2500542969140584234710605)
            ·
              refine ⟨937703613427719088016477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2500542969140584234710605 937703613427719088016477)
              ·
                refine ⟨351638855035394658006179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 937703613427719088016477 351638855035394658006179)
                ·
                  refine ⟨527458282553091987009269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351638855035394658006179 527458282553091987009269)
                  ·
                    refine ⟨49449213989352373782119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 527458282553091987009269 49449213989352373782119)
                    ·
                      rfl

theorem cell22_144453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_144453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144453 prefixEnd_144453 := by exact prefixLift 144453
  have htrace : WordTrace (prefixWord ++ tailWord_144453) baseStart_144453 baseEnd_144453 := by
    simpa [prefixWord, tailWord_144453, baseEnd_144453] using wordTrace_append hprefix tailTrace_144453
  have hstable : (prefixWord ++ tailWord_144453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144453).length < 2 ^ (prefixWord ++ tailWord_144453).sum := by decide
  have hdescent : baseEnd_144453 < baseStart_144453 := by decide
  rcases family_descends (prefixWord ++ tailWord_144453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144487 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 2, 3]
def baseStart_144487 : Nat := 118140960795 + 144487 * 2 ^ 59
def prefixEnd_144487 : Nat := 4983230072969 + 3 ^ 40 * 144487 * 2
def baseEnd_144487 : Nat := 49460852884187618432015

theorem tailTrace_144487 : CollatzResearch.WordTrace tailWord_144487 prefixEnd_144487 49460852884187618432015 := by
  unfold tailWord_144487
  simp only [CollatzResearch.WordTrace]
  refine ⟨5269873827555750260119715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3513249218370500173413143 5269873827555750260119715)
  ·
    refine ⟨7904810741333625390179573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5269873827555750260119715 7904810741333625390179573)
    ·
      refine ⟨741076007000027380329335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7904810741333625390179573 741076007000027380329335)
      ·
        refine ⟨1111614010500041070494003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741076007000027380329335 1111614010500041070494003)
        ·
          refine ⟨1667421015750061605741005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111614010500041070494003 1667421015750061605741005)
          ·
            refine ⟨625282880906273102152877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1667421015750061605741005 625282880906273102152877)
            ·
              refine ⟨234481080339852413307329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625282880906273102152877 234481080339852413307329)
              ·
                refine ⟨175860810254889309980497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234481080339852413307329 175860810254889309980497)
                ·
                  refine ⟨131895607691166982485373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175860810254889309980497 131895607691166982485373)
                  ·
                    refine ⟨49460852884187618432015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131895607691166982485373 49460852884187618432015)
                    ·
                      rfl

theorem cell22_144487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_144487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144487 prefixEnd_144487 := by exact prefixLift 144487
  have htrace : WordTrace (prefixWord ++ tailWord_144487) baseStart_144487 baseEnd_144487 := by
    simpa [prefixWord, tailWord_144487, baseEnd_144487] using wordTrace_append hprefix tailTrace_144487
  have hstable : (prefixWord ++ tailWord_144487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144487).length < 2 ^ (prefixWord ++ tailWord_144487).sum := by decide
  have hdescent : baseEnd_144487 < baseStart_144487 := by decide
  rcases family_descends (prefixWord ++ tailWord_144487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144515 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 3, 3]
def baseStart_144515 : Nat := 118140960795 + 144515 * 2 ^ 59
def prefixEnd_144515 : Nat := 4983230072969 + 3 ^ 40 * 144515 * 2
def baseEnd_144515 : Nat := 49470437856404878731929

theorem tailTrace_144515 : CollatzResearch.WordTrace tailWord_144515 prefixEnd_144515 49470437856404878731929 := by
  unfold tailWord_144515
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270895071454311042138999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3513930047636207361425999 5270895071454311042138999)
  ·
    refine ⟨7906342607181466563208499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5270895071454311042138999 7906342607181466563208499)
    ·
      refine ⟨11859513910772199844812749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7906342607181466563208499 11859513910772199844812749)
      ·
        refine ⟨4447317716539574941804781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11859513910772199844812749 4447317716539574941804781)
        ·
          refine ⟨1667744143702340603176793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4447317716539574941804781 1667744143702340603176793)
          ·
            refine ⟨1250808107776755452382595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667744143702340603176793 1250808107776755452382595)
            ·
              refine ⟨1876212161665133178573893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250808107776755452382595 1876212161665133178573893)
              ·
                refine ⟨351789780312212470982605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1876212161665133178573893 351789780312212470982605)
                ·
                  refine ⟨131921167617079676618477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351789780312212470982605 131921167617079676618477)
                  ·
                    refine ⟨49470437856404878731929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131921167617079676618477 49470437856404878731929)
                    ·
                      rfl

theorem cell22_144515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 3].length) (baseStart_144515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144515 prefixEnd_144515 := by exact prefixLift 144515
  have htrace : WordTrace (prefixWord ++ tailWord_144515) baseStart_144515 baseEnd_144515 := by
    simpa [prefixWord, tailWord_144515, baseEnd_144515] using wordTrace_append hprefix tailTrace_144515
  have hstable : (prefixWord ++ tailWord_144515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144515).length < 2 ^ (prefixWord ++ tailWord_144515).sum := by decide
  have hdescent : baseEnd_144515 < baseStart_144515 := by decide
  rcases family_descends (prefixWord ++ tailWord_144515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144517 : List Nat := [1, 3, 1, 1, 6, 2, 2, 6]
def baseStart_144517 : Nat := 118140960795 + 144517 * 2 ^ 59
def prefixEnd_144517 : Nat := 4983230072969 + 3 ^ 40 * 144517 * 2
def baseEnd_144517 : Nat := 5496791388586393353547

theorem tailTrace_144517 : CollatzResearch.WordTrace tailWord_144517 prefixEnd_144517 5496791388586393353547 := by
  unfold tailWord_144517
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270968017447065383711805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3513978678298043589141203 5270968017447065383711805)
  ·
    refine ⟨1976613006542649518891927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5270968017447065383711805 1976613006542649518891927)
    ·
      refine ⟨2964919509813974278337891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976613006542649518891927 2964919509813974278337891)
      ·
        refine ⟨4447379264720961417506837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964919509813974278337891 4447379264720961417506837)
        ·
          refine ⟨208470903033795066445633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4447379264720961417506837 208470903033795066445633)
          ·
            refine ⟨156353177275346299834225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208470903033795066445633 156353177275346299834225)
            ·
              refine ⟨117264882956509724875669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156353177275346299834225 117264882956509724875669)
              ·
                refine ⟨5496791388586393353547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117264882956509724875669 5496791388586393353547)
                ·
                  rfl

theorem cell22_144517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 6].length) (baseStart_144517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144517 prefixEnd_144517 := by exact prefixLift 144517
  have htrace : WordTrace (prefixWord ++ tailWord_144517) baseStart_144517 baseEnd_144517 := by
    simpa [prefixWord, tailWord_144517, baseEnd_144517] using wordTrace_append hprefix tailTrace_144517
  have hstable : (prefixWord ++ tailWord_144517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144517).length < 2 ^ (prefixWord ++ tailWord_144517).sum := by decide
  have hdescent : baseEnd_144517 < baseStart_144517 := by decide
  rcases family_descends (prefixWord ++ tailWord_144517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144545 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 5]
def baseStart_144545 : Nat := 118140960795 + 144545 * 2 ^ 59
def prefixEnd_144545 : Nat := 4983230072969 + 3 ^ 40 * 144545 * 2
def baseEnd_144545 : Nat := 16493569156498266827279

theorem tailTrace_144545 : CollatzResearch.WordTrace tailWord_144545 prefixEnd_144545 16493569156498266827279 := by
  unfold tailWord_144545
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271989261345626165731089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3514659507563750777154059 5271989261345626165731089)
  ·
    refine ⟨3953991946009219624298317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5271989261345626165731089 3953991946009219624298317)
    ·
      refine ⟨1482746979753457359111869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3953991946009219624298317 1482746979753457359111869)
      ·
        refine ⟨556030117407546509666951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1482746979753457359111869 556030117407546509666951)
        ·
          refine ⟨834045176111319764500427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556030117407546509666951 834045176111319764500427)
          ·
            refine ⟨1251067764166979646750641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834045176111319764500427 1251067764166979646750641)
            ·
              refine ⟨938300823125234735062981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251067764166979646750641 938300823125234735062981)
              ·
                refine ⟨175931404335981512824309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 938300823125234735062981 175931404335981512824309)
                ·
                  refine ⟨16493569156498266827279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175931404335981512824309 16493569156498266827279)
                  ·
                    rfl

theorem cell22_144545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_144545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144545 prefixEnd_144545 := by exact prefixLift 144545
  have htrace : WordTrace (prefixWord ++ tailWord_144545) baseStart_144545 baseEnd_144545 := by
    simpa [prefixWord, tailWord_144545, baseEnd_144545] using wordTrace_append hprefix tailTrace_144545
  have hstable : (prefixWord ++ tailWord_144545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144545).length < 2 ^ (prefixWord ++ tailWord_144545).sum := by decide
  have hdescent : baseEnd_144545 < baseStart_144545 := by decide
  rcases family_descends (prefixWord ++ tailWord_144545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144562 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_144562 : Nat := 118140960795 + 144562 * 2 ^ 59
def prefixEnd_144562 : Nat := 4983230072969 + 3 ^ 40 * 144562 * 2
def baseEnd_144562 : Nat := 16495508972304140935595

theorem tailTrace_144562 : CollatzResearch.WordTrace tailWord_144562 prefixEnd_144562 16495508972304140935595 := by
  unfold tailWord_144562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318152325571009517274985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3515072868189358712733293 1318152325571009517274985)
  ·
    refine ⟨988614244178257137956239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1318152325571009517274985 988614244178257137956239)
    ·
      refine ⟨1482921366267385706934359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988614244178257137956239 1482921366267385706934359)
      ·
        refine ⟨2224382049401078560401539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482921366267385706934359 2224382049401078560401539)
        ·
          refine ⟨3336573074101617840602309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224382049401078560401539 3336573074101617840602309)
          ·
            refine ⟨625607451394053345112933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3336573074101617840602309 625607451394053345112933)
            ·
              refine ⟨117301397136385002208675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 625607451394053345112933 117301397136385002208675)
              ·
                refine ⟨175952095704577503313013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117301397136385002208675 175952095704577503313013)
                ·
                  refine ⟨16495508972304140935595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175952095704577503313013 16495508972304140935595)
                  ·
                    rfl

theorem cell22_144562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_144562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144562 prefixEnd_144562 := by exact prefixLift 144562
  have htrace : WordTrace (prefixWord ++ tailWord_144562) baseStart_144562 baseEnd_144562 := by
    simpa [prefixWord, tailWord_144562, baseEnd_144562] using wordTrace_append hprefix tailTrace_144562
  have hstable : (prefixWord ++ tailWord_144562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144562).length < 2 ^ (prefixWord ++ tailWord_144562).sum := by decide
  have hdescent : baseEnd_144562 < baseStart_144562 := by decide
  rcases family_descends (prefixWord ++ tailWord_144562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144744 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_144744 : Nat := 118140960795 + 144744 * 2 ^ 59
def prefixEnd_144744 : Nat := 4983230072969 + 3 ^ 40 * 144744 * 2
def baseEnd_144744 : Nat := 49548829236324614756227

theorem tailTrace_144744 : CollatzResearch.WordTrace tailWord_144744 prefixEnd_144744 49548829236324614756227 := by
  unfold tailWord_144744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2639623693812341576112643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3519498258416455434816857 2639623693812341576112643)
  ·
    refine ⟨3959435540718512364168965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2639623693812341576112643 3959435540718512364168965)
    ·
      refine ⟨742394163884721068281681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3959435540718512364168965 742394163884721068281681)
      ·
        refine ⟨556795622913540801211261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 742394163884721068281681 556795622913540801211261)
        ·
          refine ⟨208798358592577800454223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 556795622913540801211261 208798358592577800454223)
          ·
            refine ⟨313197537888866700681335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208798358592577800454223 313197537888866700681335)
            ·
              refine ⟨469796306833300051022003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313197537888866700681335 469796306833300051022003)
              ·
                refine ⟨704694460249950076533005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469796306833300051022003 704694460249950076533005)
                ·
                  refine ⟨264260422593731278699877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704694460249950076533005 264260422593731278699877)
                  ·
                    refine ⟨49548829236324614756227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264260422593731278699877 49548829236324614756227)
                    ·
                      rfl

theorem cell22_144744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_144744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144744 prefixEnd_144744 := by exact prefixLift 144744
  have htrace : WordTrace (prefixWord ++ tailWord_144744) baseStart_144744 baseEnd_144744 := by
    simpa [prefixWord, tailWord_144744, baseEnd_144744] using wordTrace_append hprefix tailTrace_144744
  have hstable : (prefixWord ++ tailWord_144744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144744).length < 2 ^ (prefixWord ++ tailWord_144744).sum := by decide
  have hdescent : baseEnd_144744 < baseStart_144744 := by decide
  rcases family_descends (prefixWord ++ tailWord_144744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144776 : List Nat := [2, 1, 3, 3, 1, 2, 4, 2, 4]
def baseStart_144776 : Nat := 118140960795 + 144776 * 2 ^ 59
def prefixEnd_144776 : Nat := 4983230072969 + 3 ^ 40 * 144776 * 2
def baseEnd_144776 : Nat := 16519927830095732652043

theorem tailTrace_144776 : CollatzResearch.WordTrace tailWord_144776 prefixEnd_144776 16519927830095732652043 := by
  unfold tailWord_144776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640207261754376308695091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3520276349005835078260121 2640207261754376308695091)
  ·
    refine ⟨3960310892631564463042637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640207261754376308695091 3960310892631564463042637)
    ·
      refine ⟨1485116584736836673640989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3960310892631564463042637 1485116584736836673640989)
      ·
        refine ⟨556918719276313752615371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1485116584736836673640989 556918719276313752615371)
        ·
          refine ⟨835378078914470628923057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556918719276313752615371 835378078914470628923057)
          ·
            refine ⟨626533559185852971692293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835378078914470628923057 626533559185852971692293)
            ·
              refine ⟨117475042347347432192305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 626533559185852971692293 117475042347347432192305)
              ·
                refine ⟨88106281760510574144229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117475042347347432192305 88106281760510574144229)
                ·
                  refine ⟨16519927830095732652043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88106281760510574144229 16519927830095732652043)
                  ·
                    rfl

theorem cell22_144776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_144776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144776 prefixEnd_144776 := by exact prefixLift 144776
  have htrace : WordTrace (prefixWord ++ tailWord_144776) baseStart_144776 baseEnd_144776 := by
    simpa [prefixWord, tailWord_144776, baseEnd_144776] using wordTrace_append hprefix tailTrace_144776
  have hstable : (prefixWord ++ tailWord_144776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144776).length < 2 ^ (prefixWord ++ tailWord_144776).sum := by decide
  have hdescent : baseEnd_144776 < baseStart_144776 := by decide
  rcases family_descends (prefixWord ++ tailWord_144776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144836 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_144836 : Nat := 118140960795 + 144836 * 2 ^ 59
def prefixEnd_144836 : Nat := 4983230072969 + 3 ^ 40 * 144836 * 2
def baseEnd_144836 : Nat := 49580322716467041455945

theorem tailTrace_144836 : CollatzResearch.WordTrace tailWord_144836 prefixEnd_144836 49580322716467041455945 := by
  unfold tailWord_144836
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641301451645691432287181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3521735268860921909716241 2641301451645691432287181)
  ·
    refine ⟨990488044367134287107693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2641301451645691432287181 990488044367134287107693)
    ·
      refine ⟨371433016637675357665385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 990488044367134287107693 371433016637675357665385)
      ·
        refine ⟨278574762478256518249039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371433016637675357665385 278574762478256518249039)
        ·
          refine ⟨417862143717384777373559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278574762478256518249039 417862143717384777373559)
          ·
            refine ⟨626793215576077166060339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417862143717384777373559 626793215576077166060339)
            ·
              refine ⟨940189823364115749090509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626793215576077166060339 940189823364115749090509)
              ·
                refine ⟨352571183761543405908941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940189823364115749090509 352571183761543405908941)
                ·
                  refine ⟨132214193910578777215853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352571183761543405908941 132214193910578777215853)
                  ·
                    refine ⟨49580322716467041455945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132214193910578777215853 49580322716467041455945)
                    ·
                      rfl

theorem cell22_144836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_144836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144836 prefixEnd_144836 := by exact prefixLift 144836
  have htrace : WordTrace (prefixWord ++ tailWord_144836) baseStart_144836 baseEnd_144836 := by
    simpa [prefixWord, tailWord_144836, baseEnd_144836] using wordTrace_append hprefix tailTrace_144836
  have hstable : (prefixWord ++ tailWord_144836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144836).length < 2 ^ (prefixWord ++ tailWord_144836).sum := by decide
  have hdescent : baseEnd_144836 < baseStart_144836 := by decide
  rcases family_descends (prefixWord ++ tailWord_144836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144847 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 2, 5]
def baseStart_144847 : Nat := 118140960795 + 144847 * 2 ^ 59
def prefixEnd_144847 : Nat := 4983230072969 + 3 ^ 40 * 144847 * 2
def baseEnd_144847 : Nat := 49584088241266679430911

theorem tailTrace_144847 : CollatzResearch.WordTrace tailWord_144847 prefixEnd_144847 49584088241266679430911 := by
  unfold tailWord_144847
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283004106251531743224795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3522002737501021162149863 5283004106251531743224795)
  ·
    refine ⟨7924506159377297614837193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5283004106251531743224795 7924506159377297614837193)
    ·
      refine ⟨5943379619532973211127895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7924506159377297614837193 5943379619532973211127895)
      ·
        refine ⟨8915069429299459816691843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5943379619532973211127895 8915069429299459816691843)
        ·
          refine ⟨13372604143949189725037765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8915069429299459816691843 13372604143949189725037765)
          ·
            refine ⟨2507363276990473073444581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13372604143949189725037765 2507363276990473073444581)
            ·
              refine ⟨470130614435713701270859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2507363276990473073444581 470130614435713701270859)
              ·
                refine ⟨705195921653570551906289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470130614435713701270859 705195921653570551906289)
                ·
                  refine ⟨528896941240177913929717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705195921653570551906289 528896941240177913929717)
                  ·
                    refine ⟨49584088241266679430911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 528896941240177913929717 49584088241266679430911)
                    ·
                      rfl

theorem cell22_144847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_144847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144847 prefixEnd_144847 := by exact prefixLift 144847
  have htrace : WordTrace (prefixWord ++ tailWord_144847) baseStart_144847 baseEnd_144847 := by
    simpa [prefixWord, tailWord_144847, baseEnd_144847] using wordTrace_append hprefix tailTrace_144847
  have hstable : (prefixWord ++ tailWord_144847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144847).length < 2 ^ (prefixWord ++ tailWord_144847).sum := by decide
  have hdescent : baseEnd_144847 < baseStart_144847 := by decide
  rcases family_descends (prefixWord ++ tailWord_144847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144879 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 1, 4]
def baseStart_144879 : Nat := 118140960795 + 144879 * 2 ^ 59
def prefixEnd_144879 : Nat := 4983230072969 + 3 ^ 40 * 144879 * 2
def baseEnd_144879 : Nat := 49595042495229262630813

theorem tailTrace_144879 : CollatzResearch.WordTrace tailWord_144879 prefixEnd_144879 49595042495229262630813 := by
  unfold tailWord_144879
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284171242135601208389691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3522780828090400805593127 5284171242135601208389691)
  ·
    refine ⟨7926256863203401812584537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5284171242135601208389691 7926256863203401812584537)
    ·
      refine ⟨5944692647402551359438403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7926256863203401812584537 5944692647402551359438403)
      ·
        refine ⟨8917038971103827039157605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5944692647402551359438403 8917038971103827039157605)
        ·
          refine ⟨1671944807081967569842051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8917038971103827039157605 1671944807081967569842051)
          ·
            refine ⟨2507917210622951354763077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671944807081967569842051 2507917210622951354763077)
            ·
              refine ⟨470234476991803379018077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2507917210622951354763077 470234476991803379018077)
              ·
                refine ⟨176337928871926267131779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 470234476991803379018077 176337928871926267131779)
                ·
                  refine ⟨264506893307889400697669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176337928871926267131779 264506893307889400697669)
                  ·
                    refine ⟨49595042495229262630813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264506893307889400697669 49595042495229262630813)
                    ·
                      rfl

theorem cell22_144879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_144879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144879 prefixEnd_144879 := by exact prefixLift 144879
  have htrace : WordTrace (prefixWord ++ tailWord_144879) baseStart_144879 baseEnd_144879 := by
    simpa [prefixWord, tailWord_144879, baseEnd_144879] using wordTrace_append hprefix tailTrace_144879
  have hstable : (prefixWord ++ tailWord_144879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144879).length < 2 ^ (prefixWord ++ tailWord_144879).sum := by decide
  have hdescent : baseEnd_144879 < baseStart_144879 := by decide
  rcases family_descends (prefixWord ++ tailWord_144879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144900 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 5]
def baseStart_144900 : Nat := 118140960795 + 144900 * 2 ^ 59
def prefixEnd_144900 : Nat := 4983230072969 + 3 ^ 40 * 144900 * 2
def baseEnd_144900 : Nat := 16534077074797402618583

theorem tailTrace_144900 : CollatzResearch.WordTrace tailWord_144900 prefixEnd_144900 16534077074797402618583 := by
  unfold tailWord_144900
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642468587529760897452077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3523291450039681196602769 2642468587529760897452077)
  ·
    refine ⟨990925720323660336544529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2642468587529760897452077 990925720323660336544529)
    ·
      refine ⟨743194290242745252408397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 990925720323660336544529 743194290242745252408397)
      ·
        refine ⟨278697858841029469653149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 743194290242745252408397 278697858841029469653149)
        ·
          refine ⟨104511697065386051119931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278697858841029469653149 104511697065386051119931)
          ·
            refine ⟨156767545598079076679897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104511697065386051119931 156767545598079076679897)
            ·
              refine ⟨117575659198559307509923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156767545598079076679897 117575659198559307509923)
              ·
                refine ⟨176363488797838961264885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117575659198559307509923 176363488797838961264885)
                ·
                  refine ⟨16534077074797402618583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176363488797838961264885 16534077074797402618583)
                  ·
                    rfl

theorem cell22_144900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_144900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144900 prefixEnd_144900 := by exact prefixLift 144900
  have htrace : WordTrace (prefixWord ++ tailWord_144900) baseStart_144900 baseEnd_144900 := by
    simpa [prefixWord, tailWord_144900, baseEnd_144900] using wordTrace_append hprefix tailTrace_144900
  have hstable : (prefixWord ++ tailWord_144900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144900).length < 2 ^ (prefixWord ++ tailWord_144900).sum := by decide
  have hdescent : baseEnd_144900 < baseStart_144900 := by decide
  rcases family_descends (prefixWord ++ tailWord_144900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144956 : List Nat := [2, 2, 2, 2, 4, 2, 1, 7]
def baseStart_144956 : Nat := 118140960795 + 144956 * 2 ^ 59
def prefixEnd_144956 : Nat := 4983230072969 + 3 ^ 40 * 144956 * 2
def baseEnd_144956 : Nat := 5513489018758525383953

theorem tailTrace_144956 : CollatzResearch.WordTrace tailWord_144956 prefixEnd_144956 5513489018758525383953 := by
  unfold tailWord_144956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643489831428321679471361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3524653108571095572628481 2643489831428321679471361)
  ·
    refine ⟨1982617373571241259603521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2643489831428321679471361 1982617373571241259603521)
    ·
      refine ⟨1486963030178430944702641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1982617373571241259603521 1486963030178430944702641)
      ·
        refine ⟨1115222272633823208526981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1486963030178430944702641 1115222272633823208526981)
        ·
          refine ⟨209104176118841851598809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1115222272633823208526981 209104176118841851598809)
          ·
            refine ⟨156828132089131388699107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209104176118841851598809 156828132089131388699107)
            ·
              refine ⟨235242198133697083048661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156828132089131388699107 235242198133697083048661)
              ·
                refine ⟨5513489018758525383953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 235242198133697083048661 5513489018758525383953)
                ·
                  rfl

theorem cell22_144956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 7].length) (baseStart_144956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144956 prefixEnd_144956 := by exact prefixLift 144956
  have htrace : WordTrace (prefixWord ++ tailWord_144956) baseStart_144956 baseEnd_144956 := by
    simpa [prefixWord, tailWord_144956, baseEnd_144956] using wordTrace_append hprefix tailTrace_144956
  have hstable : (prefixWord ++ tailWord_144956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144956).length < 2 ^ (prefixWord ++ tailWord_144956).sum := by decide
  have hdescent : baseEnd_144956 < baseStart_144956 := by decide
  rcases family_descends (prefixWord ++ tailWord_144956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144973 : List Nat := [1, 6, 1, 1, 3, 1, 3, 6]
def baseStart_144973 : Nat := 118140960795 + 144973 * 2 ^ 59
def prefixEnd_144973 : Nat := 4983230072969 + 3 ^ 40 * 144973 * 2
def baseEnd_144973 : Nat := 5514135624027150086725

theorem tailTrace_144973 : CollatzResearch.WordTrace tailWord_144973 prefixEnd_144973 5514135624027150086725 := by
  unfold tailWord_144973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287599703795055262311573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3525066469196703508207715 5287599703795055262311573)
  ·
    refine ⟨247856236115393215420855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5287599703795055262311573 247856236115393215420855)
    ·
      refine ⟨371784354173089823131283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247856236115393215420855 371784354173089823131283)
      ·
        refine ⟨557676531259634734696925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371784354173089823131283 557676531259634734696925)
        ·
          refine ⟨209128699222363025511347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 557676531259634734696925 209128699222363025511347)
          ·
            refine ⟨313693048833544538267021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209128699222363025511347 313693048833544538267021)
            ·
              refine ⟨117634893312579201850133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 313693048833544538267021 117634893312579201850133)
              ·
                refine ⟨5514135624027150086725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117634893312579201850133 5514135624027150086725)
                ·
                  rfl

theorem cell22_144973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 6].length) (baseStart_144973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144973 prefixEnd_144973 := by exact prefixLift 144973
  have htrace : WordTrace (prefixWord ++ tailWord_144973) baseStart_144973 baseEnd_144973 := by
    simpa [prefixWord, tailWord_144973, baseEnd_144973] using wordTrace_append hprefix tailTrace_144973
  have hstable : (prefixWord ++ tailWord_144973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144973).length < 2 ^ (prefixWord ++ tailWord_144973).sum := by decide
  have hdescent : baseEnd_144973 < baseStart_144973 := by decide
  rcases family_descends (prefixWord ++ tailWord_144973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144999 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 2, 5]
def baseStart_144999 : Nat := 118140960795 + 144999 * 2 ^ 59
def prefixEnd_144999 : Nat := 4983230072969 + 3 ^ 40 * 144999 * 2
def baseEnd_144999 : Nat := 49636120947588949630445

theorem tailTrace_144999 : CollatzResearch.WordTrace tailWord_144999 prefixEnd_144999 49636120947588949630445 := by
  unfold tailWord_144999
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288548001700861702758051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3525698667800574468505367 5288548001700861702758051)
  ·
    refine ⟨7932822002551292554137077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5288548001700861702758051 7932822002551292554137077)
    ·
      refine ⟨743702062739183676950351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7932822002551292554137077 743702062739183676950351)
      ·
        refine ⟨1115553094108775515425527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743702062739183676950351 1115553094108775515425527)
        ·
          refine ⟨1673329641163163273138291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115553094108775515425527 1673329641163163273138291)
          ·
            refine ⟨2509994461744744909707437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673329641163163273138291 2509994461744744909707437)
            ·
              refine ⟨941247923154279341140289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2509994461744744909707437 941247923154279341140289)
              ·
                refine ⟨705935942365709505855217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941247923154279341140289 705935942365709505855217)
                ·
                  refine ⟨529451956774282129391413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705935942365709505855217 529451956774282129391413)
                  ·
                    refine ⟨49636120947588949630445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 529451956774282129391413 49636120947588949630445)
                    ·
                      rfl

theorem cell22_144999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_144999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_144999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_144999 prefixEnd_144999 := by exact prefixLift 144999
  have htrace : WordTrace (prefixWord ++ tailWord_144999) baseStart_144999 baseEnd_144999 := by
    simpa [prefixWord, tailWord_144999, baseEnd_144999] using wordTrace_append hprefix tailTrace_144999
  have hstable : (prefixWord ++ tailWord_144999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144999).length < 2 ^ (prefixWord ++ tailWord_144999).sum := by decide
  have hdescent : baseEnd_144999 < baseStart_144999 := by decide
  rcases family_descends (prefixWord ++ tailWord_144999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145029 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 6]
def baseStart_145029 : Nat := 118140960795 + 145029 * 2 ^ 59
def prefixEnd_145029 : Nat := 4983230072969 + 3 ^ 40 * 145029 * 2
def baseEnd_145029 : Nat := 16548796853559623793451

theorem tailTrace_145029 : CollatzResearch.WordTrace tailWord_145029 prefixEnd_145029 16548796853559623793451 := by
  unfold tailWord_145029
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289642191592176826350141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3526428127728117884233427 5289642191592176826350141)
  ·
    refine ⟨1983615821847066309881303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5289642191592176826350141 1983615821847066309881303)
    ·
      refine ⟨2975423732770599464821955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983615821847066309881303 2975423732770599464821955)
      ·
        refine ⟨4463135599155899197232933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975423732770599464821955 4463135599155899197232933)
        ·
          refine ⟨836837924841731099481175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4463135599155899197232933 836837924841731099481175)
          ·
            refine ⟨1255256887262596649221763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836837924841731099481175 1255256887262596649221763)
            ·
              refine ⟨1882885330893894973832645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255256887262596649221763 1882885330893894973832645)
              ·
                refine ⟨353040999542605307593621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1882885330893894973832645 353040999542605307593621)
                ·
                  refine ⟨16548796853559623793451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 353040999542605307593621 16548796853559623793451)
                  ·
                    rfl

theorem cell22_145029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_145029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145029 prefixEnd_145029 := by exact prefixLift 145029
  have htrace : WordTrace (prefixWord ++ tailWord_145029) baseStart_145029 baseEnd_145029 := by
    simpa [prefixWord, tailWord_145029, baseEnd_145029] using wordTrace_append hprefix tailTrace_145029
  have hstable : (prefixWord ++ tailWord_145029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145029).length < 2 ^ (prefixWord ++ tailWord_145029).sum := by decide
  have hdescent : baseEnd_145029 < baseStart_145029 := by decide
  rcases family_descends (prefixWord ++ tailWord_145029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145031 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 1, 4]
def baseStart_145031 : Nat := 118140960795 + 145031 * 2 ^ 59
def prefixEnd_145031 : Nat := 4983230072969 + 3 ^ 40 * 145031 * 2
def baseEnd_145031 : Nat := 49647075201551532830347

theorem tailTrace_145031 : CollatzResearch.WordTrace tailWord_145031 prefixEnd_145031 49647075201551532830347 := by
  unfold tailWord_145031
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289715137584931167922947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3526476758389954111948631 5289715137584931167922947)
  ·
    refine ⟨7934572706377396751884421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5289715137584931167922947 7934572706377396751884421)
    ·
      refine ⟨1487732382445761890978329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7934572706377396751884421 1487732382445761890978329)
      ·
        refine ⟨1115799286834321418233747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1487732382445761890978329 1115799286834321418233747)
        ·
          refine ⟨1673698930251482127350621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115799286834321418233747 1673698930251482127350621)
          ·
            refine ⟨627637098844305797756483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1673698930251482127350621 627637098844305797756483)
            ·
              refine ⟨941455648266458696634725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627637098844305797756483 941455648266458696634725)
              ·
                refine ⟨176522934049961005619011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 941455648266458696634725 176522934049961005619011)
                ·
                  refine ⟨264784401074941508428517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176522934049961005619011 264784401074941508428517)
                  ·
                    refine ⟨49647075201551532830347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264784401074941508428517 49647075201551532830347)
                    ·
                      rfl

theorem cell22_145031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_145031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145031 prefixEnd_145031 := by exact prefixLift 145031
  have htrace : WordTrace (prefixWord ++ tailWord_145031) baseStart_145031 baseEnd_145031 := by
    simpa [prefixWord, tailWord_145031, baseEnd_145031] using wordTrace_append hprefix tailTrace_145031
  have hstable : (prefixWord ++ tailWord_145031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145031).length < 2 ^ (prefixWord ++ tailWord_145031).sum := by decide
  have hdescent : baseEnd_145031 < baseStart_145031 := by decide
  rcases family_descends (prefixWord ++ tailWord_145031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145061 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_145061 : Nat := 118140960795 + 145061 * 2 ^ 59
def prefixEnd_145061 : Nat := 4983230072969 + 3 ^ 40 * 145061 * 2
def baseEnd_145061 : Nat := 49657344814641454580255

theorem tailTrace_145061 : CollatzResearch.WordTrace tailWord_145061 prefixEnd_145061 49657344814641454580255 := by
  unfold tailWord_145061
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290809327476246291515037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3527206218317497527676691 5290809327476246291515037)
  ·
    refine ⟨1984053497803592359318139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5290809327476246291515037 1984053497803592359318139)
    ·
      refine ⟨2976080246705388538977209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984053497803592359318139 2976080246705388538977209)
      ·
        refine ⟨2232060185029041404232907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2976080246705388538977209 2232060185029041404232907)
        ·
          refine ⟨3348090277543562106349361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232060185029041404232907 3348090277543562106349361)
          ·
            refine ⟨2511067708157671579762021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3348090277543562106349361 2511067708157671579762021)
            ·
              refine ⟨470825195279563421205379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2511067708157671579762021 470825195279563421205379)
              ·
                refine ⟨706237792919345131808069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470825195279563421205379 706237792919345131808069)
                ·
                  refine ⟨132419586172377212214013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706237792919345131808069 132419586172377212214013)
                  ·
                    refine ⟨49657344814641454580255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132419586172377212214013 49657344814641454580255)
                    ·
                      rfl

theorem cell22_145061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_145061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145061 prefixEnd_145061 := by exact prefixLift 145061
  have htrace : WordTrace (prefixWord ++ tailWord_145061) baseStart_145061 baseEnd_145061 := by
    simpa [prefixWord, tailWord_145061, baseEnd_145061] using wordTrace_append hprefix tailTrace_145061
  have hstable : (prefixWord ++ tailWord_145061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145061).length < 2 ^ (prefixWord ++ tailWord_145061).sum := by decide
  have hdescent : baseEnd_145061 < baseStart_145061 := by decide
  rcases family_descends (prefixWord ++ tailWord_145061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145074 : List Nat := [3, 2, 1, 1, 1, 2, 3, 9]
def baseStart_145074 : Nat := 118140960795 + 145074 * 2 ^ 59
def prefixEnd_145074 : Nat := 4983230072969 + 3 ^ 40 * 145074 * 2
def baseEnd_145074 : Nat := 5517977220034861556135

theorem tailTrace_145074 : CollatzResearch.WordTrace tailWord_145074 prefixEnd_145074 5517977220034861556135 := by
  unfold tailWord_145074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322820869107287377934569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3527522317619433007825517 1322820869107287377934569)
  ·
    refine ⟨992115651830465533450927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1322820869107287377934569 992115651830465533450927)
    ·
      refine ⟨1488173477745698300176391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992115651830465533450927 1488173477745698300176391)
      ·
        refine ⟨2232260216618547450264587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488173477745698300176391 2232260216618547450264587)
        ·
          refine ⟨3348390324927821175396881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232260216618547450264587 3348390324927821175396881)
          ·
            refine ⟨2511292743695865881547661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3348390324927821175396881 2511292743695865881547661)
            ·
              refine ⟨941734778885949705580373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2511292743695865881547661 941734778885949705580373)
              ·
                refine ⟨5517977220034861556135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 941734778885949705580373 5517977220034861556135)
                ·
                  rfl

theorem cell22_145074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_145074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145074 prefixEnd_145074 := by exact prefixLift 145074
  have htrace : WordTrace (prefixWord ++ tailWord_145074) baseStart_145074 baseEnd_145074 := by
    simpa [prefixWord, tailWord_145074, baseEnd_145074] using wordTrace_append hprefix tailTrace_145074
  have hstable : (prefixWord ++ tailWord_145074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145074).length < 2 ^ (prefixWord ++ tailWord_145074).sum := by decide
  have hdescent : baseEnd_145074 < baseStart_145074 := by decide
  rcases family_descends (prefixWord ++ tailWord_145074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145170 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_145170 : Nat := 118140960795 + 145170 * 2 ^ 59
def prefixEnd_145170 : Nat := 4983230072969 + 3 ^ 40 * 145170 * 2
def baseEnd_145170 : Nat := 16564885914067167868307

theorem tailTrace_145170 : CollatzResearch.WordTrace tailWord_145170 prefixEnd_145170 16564885914067167868307 := by
  unfold tailWord_145170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323696221020339476808241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3529856589387571938155309 1323696221020339476808241)
  ·
    refine ⟨992772165765254607606181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1323696221020339476808241 992772165765254607606181)
    ·
      refine ⟨186144781080985238926159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 992772165765254607606181 186144781080985238926159)
      ·
        refine ⟨279217171621477858389239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186144781080985238926159 279217171621477858389239)
        ·
          refine ⟨418825757432216787583859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279217171621477858389239 418825757432216787583859)
          ·
            refine ⟨628238636148325181375789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418825757432216787583859 628238636148325181375789)
            ·
              refine ⟨235589488555621943015921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 628238636148325181375789 235589488555621943015921)
              ·
                refine ⟨176692116416716457261941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235589488555621943015921 176692116416716457261941)
                ·
                  refine ⟨16564885914067167868307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176692116416716457261941 16564885914067167868307)
                  ·
                    rfl

theorem cell22_145170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_145170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145170 prefixEnd_145170 := by exact prefixLift 145170
  have htrace : WordTrace (prefixWord ++ tailWord_145170) baseStart_145170 baseEnd_145170 := by
    simpa [prefixWord, tailWord_145170, baseEnd_145170] using wordTrace_append hprefix tailTrace_145170
  have hstable : (prefixWord ++ tailWord_145170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145170).length < 2 ^ (prefixWord ++ tailWord_145170).sum := by decide
  have hdescent : baseEnd_145170 < baseStart_145170 := by decide
  rcases family_descends (prefixWord ++ tailWord_145170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145247 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 2, 3]
def baseStart_145247 : Nat := 118140960795 + 145247 * 2 ^ 59
def prefixEnd_145247 : Nat := 4983230072969 + 3 ^ 40 * 145247 * 2
def baseEnd_145247 : Nat := 49721016415798969429685

theorem tailTrace_145247 : CollatzResearch.WordTrace tailWord_145247 prefixEnd_145247 49721016415798969429685 := by
  unfold tailWord_145247
  simp only [CollatzResearch.WordTrace]
  refine ⟨5297593304802400057785995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3531728869868266705190663 5297593304802400057785995)
  ·
    refine ⟨7946389957203600086678993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5297593304802400057785995 7946389957203600086678993)
    ·
      refine ⟨5959792467902700065009245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7946389957203600086678993 5959792467902700065009245)
      ·
        refine ⟨2234922175463512524378467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5959792467902700065009245 2234922175463512524378467)
        ·
          refine ⟨3352383263195268786567701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234922175463512524378467 3352383263195268786567701)
          ·
            refine ⟨157142965462278224370361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3352383263195268786567701 157142965462278224370361)
            ·
              refine ⟨117857224096708668277771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157142965462278224370361 117857224096708668277771)
              ·
                refine ⟨176785836145063002416657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117857224096708668277771 176785836145063002416657)
                ·
                  refine ⟨132589377108797251812493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176785836145063002416657 132589377108797251812493)
                  ·
                    refine ⟨49721016415798969429685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132589377108797251812493 49721016415798969429685)
                    ·
                      rfl

theorem cell22_145247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_145247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145247 prefixEnd_145247 := by exact prefixLift 145247
  have htrace : WordTrace (prefixWord ++ tailWord_145247) baseStart_145247 baseEnd_145247 := by
    simpa [prefixWord, tailWord_145247, baseEnd_145247] using wordTrace_append hprefix tailTrace_145247
  have hstable : (prefixWord ++ tailWord_145247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145247).length < 2 ^ (prefixWord ++ tailWord_145247).sum := by decide
  have hdescent : baseEnd_145247 < baseStart_145247 := by decide
  rcases family_descends (prefixWord ++ tailWord_145247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145275 : List Nat := [1, 1, 1, 1, 1, 5, 1, 7, 1, 3]
def baseStart_145275 : Nat := 118140960795 + 145275 * 2 ^ 59
def prefixEnd_145275 : Nat := 4983230072969 + 3 ^ 40 * 145275 * 2
def baseEnd_145275 : Nat := 49730601388016229729599

theorem tailTrace_145275 : CollatzResearch.WordTrace tailWord_145275 prefixEnd_145275 49730601388016229729599 := by
  unfold tailWord_145275
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298614548700960839805279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3532409699133973893203519 5298614548700960839805279)
  ·
    refine ⟨7947921823051441259707919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5298614548700960839805279 7947921823051441259707919)
    ·
      refine ⟨11921882734577161889561879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7947921823051441259707919 11921882734577161889561879)
      ·
        refine ⟨17882824101865742834342819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11921882734577161889561879 17882824101865742834342819)
        ·
          refine ⟨26824236152798614251514229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17882824101865742834342819 26824236152798614251514229)
          ·
            refine ⟨2514772139324870086079459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26824236152798614251514229 2514772139324870086079459)
            ·
              refine ⟨3772158208987305129119189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514772139324870086079459 3772158208987305129119189)
              ·
                refine ⟨88409958023139963963731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3772158208987305129119189 88409958023139963963731)
                ·
                  refine ⟨132614937034709945945597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88409958023139963963731 132614937034709945945597)
                  ·
                    refine ⟨49730601388016229729599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132614937034709945945597 49730601388016229729599)
                    ·
                      rfl

theorem cell22_145275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 3].length) (baseStart_145275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145275 prefixEnd_145275 := by exact prefixLift 145275
  have htrace : WordTrace (prefixWord ++ tailWord_145275) baseStart_145275 baseEnd_145275 := by
    simpa [prefixWord, tailWord_145275, baseEnd_145275] using wordTrace_append hprefix tailTrace_145275
  have hstable : (prefixWord ++ tailWord_145275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145275).length < 2 ^ (prefixWord ++ tailWord_145275).sum := by decide
  have hdescent : baseEnd_145275 < baseStart_145275 := by decide
  rcases family_descends (prefixWord ++ tailWord_145275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145303 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 2, 5]
def baseStart_145303 : Nat := 118140960795 + 145303 * 2 ^ 59
def prefixEnd_145303 : Nat := 4983230072969 + 3 ^ 40 * 145303 * 2
def baseEnd_145303 : Nat := 49740186360233490029513

theorem tailTrace_145303 : CollatzResearch.WordTrace tailWord_145303 prefixEnd_145303 49740186360233490029513 := by
  unfold tailWord_145303
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299635792599521621824563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3533090528399681081216375 5299635792599521621824563)
  ·
    refine ⟨7949453688899282432736845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5299635792599521621824563 7949453688899282432736845)
    ·
      refine ⟨2981045133337230912276317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7949453688899282432736845 2981045133337230912276317)
      ·
        refine ⟨1117891925001461592103619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2981045133337230912276317 1117891925001461592103619)
        ·
          refine ⟨1676837887502192388155429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117891925001461592103619 1676837887502192388155429)
          ·
            refine ⟨314407103906661072779143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1676837887502192388155429 314407103906661072779143)
            ·
              refine ⟨471610655859991609168715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314407103906661072779143 471610655859991609168715)
              ·
                refine ⟨707415983789987413753073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471610655859991609168715 707415983789987413753073)
                ·
                  refine ⟨530561987842490560314805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707415983789987413753073 530561987842490560314805)
                  ·
                    refine ⟨49740186360233490029513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 530561987842490560314805 49740186360233490029513)
                    ·
                      rfl

theorem cell22_145303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_145303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145303 prefixEnd_145303 := by exact prefixLift 145303
  have htrace : WordTrace (prefixWord ++ tailWord_145303) baseStart_145303 baseEnd_145303 := by
    simpa [prefixWord, tailWord_145303, baseEnd_145303] using wordTrace_append hprefix tailTrace_145303
  have hstable : (prefixWord ++ tailWord_145303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145303).length < 2 ^ (prefixWord ++ tailWord_145303).sum := by decide
  have hdescent : baseEnd_145303 < baseStart_145303 := by decide
  rcases family_descends (prefixWord ++ tailWord_145303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145365 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_145365 : Nat := 118140960795 + 145365 * 2 ^ 59
def prefixEnd_145365 : Nat := 4983230072969 + 3 ^ 40 * 145365 * 2
def baseEnd_145365 : Nat := 49761410227285994979323

theorem tailTrace_145365 : CollatzResearch.WordTrace tailWord_145365 prefixEnd_145365 49761410227285994979323 := by
  unfold tailWord_145365
  simp only [CollatzResearch.WordTrace]
  refine ⟨5301897118374906210581549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3534598078916604140387699 5301897118374906210581549)
  ·
    refine ⟨1988211419390589828968081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5301897118374906210581549 1988211419390589828968081)
    ·
      refine ⟨1491158564542942371726061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1988211419390589828968081 1491158564542942371726061)
      ·
        refine ⟨559184461703603389397273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1491158564542942371726061 559184461703603389397273)
        ·
          refine ⟨419388346277702542047955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559184461703603389397273 419388346277702542047955)
          ·
            refine ⟨629082519416553813071933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419388346277702542047955 629082519416553813071933)
            ·
              refine ⟨235905944781207679901975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 629082519416553813071933 235905944781207679901975)
              ·
                refine ⟨353858917171811519852963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235905944781207679901975 353858917171811519852963)
                ·
                  refine ⟨530788375757717279779445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353858917171811519852963 530788375757717279779445)
                  ·
                    refine ⟨49761410227285994979323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 530788375757717279779445 49761410227285994979323)
                    ·
                      rfl

theorem cell22_145365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_145365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145365 prefixEnd_145365 := by exact prefixLift 145365
  have htrace : WordTrace (prefixWord ++ tailWord_145365) baseStart_145365 baseEnd_145365 := by
    simpa [prefixWord, tailWord_145365, baseEnd_145365] using wordTrace_append hprefix tailTrace_145365
  have hstable : (prefixWord ++ tailWord_145365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145365).length < 2 ^ (prefixWord ++ tailWord_145365).sum := by decide
  have hdescent : baseEnd_145365 < baseStart_145365 := by decide
  rcases family_descends (prefixWord ++ tailWord_145365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145412 : List Nat := [2, 3, 2, 4, 1, 1, 2, 7]
def baseStart_145412 : Nat := 118140960795 + 145412 * 2 ^ 59
def prefixEnd_145412 : Nat := 4983230072969 + 3 ^ 40 * 145412 * 2
def baseEnd_145412 : Nat := 5530833254199282117131

theorem tailTrace_145412 : CollatzResearch.WordTrace tailWord_145412 prefixEnd_145412 5530833254199282117131 := by
  unfold tailWord_145412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651805674602316618771245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3535740899469755491694993 2651805674602316618771245)
  ·
    refine ⟨994427127975868732039217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2651805674602316618771245 994427127975868732039217)
    ·
      refine ⟨745820345981901549029413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 994427127975868732039217 745820345981901549029413)
      ·
        refine ⟨139841314871606540443015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 745820345981901549029413 139841314871606540443015)
        ·
          refine ⟨209761972307409810664523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139841314871606540443015 209761972307409810664523)
          ·
            refine ⟨314642958461114715996785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209761972307409810664523 314642958461114715996785)
            ·
              refine ⟨235982218845836036997589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314642958461114715996785 235982218845836036997589)
              ·
                refine ⟨5530833254199282117131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 235982218845836036997589 5530833254199282117131)
                ·
                  rfl

theorem cell22_145412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 7].length) (baseStart_145412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145412 prefixEnd_145412 := by exact prefixLift 145412
  have htrace : WordTrace (prefixWord ++ tailWord_145412) baseStart_145412 baseEnd_145412 := by
    simpa [prefixWord, tailWord_145412, baseEnd_145412] using wordTrace_append hprefix tailTrace_145412
  have hstable : (prefixWord ++ tailWord_145412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145412).length < 2 ^ (prefixWord ++ tailWord_145412).sum := by decide
  have hdescent : baseEnd_145412 < baseStart_145412 := by decide
  rcases family_descends (prefixWord ++ tailWord_145412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145483 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 5, 5]
def baseStart_145483 : Nat := 118140960795 + 145483 * 2 ^ 59
def prefixEnd_145483 : Nat := 4983230072969 + 3 ^ 40 * 145483 * 2
def baseEnd_145483 : Nat := 49801804038773020528961

theorem tailTrace_145483 : CollatzResearch.WordTrace tailWord_145483 prefixEnd_145483 49801804038773020528961 := by
  unfold tailWord_145483
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306200931947412363377103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3537467287964941575584735 5306200931947412363377103)
  ·
    refine ⟨7959301397921118545065655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5306200931947412363377103 7959301397921118545065655)
    ·
      refine ⟨11938952096881677817598483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7959301397921118545065655 11938952096881677817598483)
      ·
        refine ⟨17908428145322516726397725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11938952096881677817598483 17908428145322516726397725)
        ·
          refine ⟨6715660554495943772399147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17908428145322516726397725 6715660554495943772399147)
          ·
            refine ⟨10073490831743915658598721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6715660554495943772399147 10073490831743915658598721)
            ·
              refine ⟨7555118123807936743949041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10073490831743915658598721 7555118123807936743949041)
              ·
                refine ⟨5666338592855952557961781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7555118123807936743949041 5666338592855952557961781)
                ·
                  refine ⟨531219243080245552308917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5666338592855952557961781 531219243080245552308917)
                  ·
                    refine ⟨49801804038773020528961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 531219243080245552308917 49801804038773020528961)
                    ·
                      rfl

theorem cell22_145483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_145483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145483 prefixEnd_145483 := by exact prefixLift 145483
  have htrace : WordTrace (prefixWord ++ tailWord_145483) baseStart_145483 baseEnd_145483 := by
    simpa [prefixWord, tailWord_145483, baseEnd_145483] using wordTrace_append hprefix tailTrace_145483
  have hstable : (prefixWord ++ tailWord_145483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145483).length < 2 ^ (prefixWord ++ tailWord_145483).sum := by decide
  have hdescent : baseEnd_145483 < baseStart_145483 := by decide
  rcases family_descends (prefixWord ++ tailWord_145483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145504 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 1, 4]
def baseStart_145504 : Nat := 118140960795 + 145504 * 2 ^ 59
def prefixEnd_145504 : Nat := 4983230072969 + 3 ^ 40 * 145504 * 2
def baseEnd_145504 : Nat := 49808992767935965753897

theorem tailTrace_145504 : CollatzResearch.WordTrace tailWord_145504 prefixEnd_145504 49808992767935965753897 := by
  unfold tailWord_145504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653483432435666474945783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3537977909914221966594377 2653483432435666474945783)
  ·
    refine ⟨3980225148653499712418675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2653483432435666474945783 3980225148653499712418675)
    ·
      refine ⟨5970337722980249568628013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980225148653499712418675 5970337722980249568628013)
      ·
        refine ⟨2238876646117593588235505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5970337722980249568628013 2238876646117593588235505)
        ·
          refine ⟨1679157484588195191176629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238876646117593588235505 1679157484588195191176629)
          ·
            refine ⟨157421014180143299172809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1679157484588195191176629 157421014180143299172809)
            ·
              refine ⟨118065760635107474379607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157421014180143299172809 118065760635107474379607)
              ·
                refine ⟨177098640952661211569411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118065760635107474379607 177098640952661211569411)
                ·
                  refine ⟨265647961428991817354117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177098640952661211569411 265647961428991817354117)
                  ·
                    refine ⟨49808992767935965753897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 265647961428991817354117 49808992767935965753897)
                    ·
                      rfl

theorem cell22_145504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_145504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145504 prefixEnd_145504 := by exact prefixLift 145504
  have htrace : WordTrace (prefixWord ++ tailWord_145504) baseStart_145504 baseEnd_145504 := by
    simpa [prefixWord, tailWord_145504, baseEnd_145504] using wordTrace_append hprefix tailTrace_145504
  have hstable : (prefixWord ++ tailWord_145504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145504).length < 2 ^ (prefixWord ++ tailWord_145504).sum := by decide
  have hdescent : baseEnd_145504 < baseStart_145504 := by decide
  rcases family_descends (prefixWord ++ tailWord_145504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145513 : List Nat := [1, 2, 1, 1, 1, 5, 11]
def baseStart_145513 : Nat := 118140960795 + 145513 * 2 ^ 59
def prefixEnd_145513 : Nat := 4983230072969 + 3 ^ 40 * 145513 * 2
def baseEnd_145513 : Nat := 1844891616735664528847

theorem tailTrace_145513 : CollatzResearch.WordTrace tailWord_145513 prefixEnd_145513 1844891616735664528847 := by
  unfold tailWord_145513
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307295121838727486969193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3538196747892484991312795 5307295121838727486969193)
  ·
    refine ⟨3980471341379045615226895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5307295121838727486969193 3980471341379045615226895)
    ·
      refine ⟨5970707012068568422840343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980471341379045615226895 5970707012068568422840343)
      ·
        refine ⟨8956060518102852634260515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970707012068568422840343 8956060518102852634260515)
        ·
          refine ⟨13434090777154278951390773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8956060518102852634260515 13434090777154278951390773)
          ·
            refine ⟨1259446010358213651692885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13434090777154278951390773 1259446010358213651692885)
            ·
              refine ⟨1844891616735664528847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1259446010358213651692885 1844891616735664528847)
              ·
                rfl

theorem cell22_145513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 11].length) (baseStart_145513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145513 prefixEnd_145513 := by exact prefixLift 145513
  have htrace : WordTrace (prefixWord ++ tailWord_145513) baseStart_145513 baseEnd_145513 := by
    simpa [prefixWord, tailWord_145513, baseEnd_145513] using wordTrace_append hprefix tailTrace_145513
  have hstable : (prefixWord ++ tailWord_145513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145513).length < 2 ^ (prefixWord ++ tailWord_145513).sum := by decide
  have hdescent : baseEnd_145513 < baseStart_145513 := by decide
  rcases family_descends (prefixWord ++ tailWord_145513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145517 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_145517 : Nat := 118140960795 + 145517 * 2 ^ 59
def prefixEnd_145517 : Nat := 4983230072969 + 3 ^ 40 * 145517 * 2
def baseEnd_145517 : Nat := 49813442933608265178857

theorem tailTrace_145517 : CollatzResearch.WordTrace tailWord_145517 prefixEnd_145517 49813442933608265178857 := by
  unfold tailWord_145517
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307441013824236170114805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3538294009216157446743203 5307441013824236170114805)
  ·
    refine ⟨497572595046022140948263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5307441013824236170114805 497572595046022140948263)
    ·
      refine ⟨746358892569033211422395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497572595046022140948263 746358892569033211422395)
      ·
        refine ⟨1119538338853549817133593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746358892569033211422395 1119538338853549817133593)
        ·
          refine ⟨839653754140162362850195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1119538338853549817133593 839653754140162362850195)
          ·
            refine ⟨1259480631210243544275293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839653754140162362850195 1259480631210243544275293)
            ·
              refine ⟨472305236703841329103235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1259480631210243544275293 472305236703841329103235)
              ·
                refine ⟨708457855055761993654853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472305236703841329103235 708457855055761993654853)
                ·
                  refine ⟨132835847822955373810285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708457855055761993654853 132835847822955373810285)
                  ·
                    refine ⟨49813442933608265178857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132835847822955373810285 49813442933608265178857)
                    ·
                      rfl

theorem cell22_145517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_145517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145517 prefixEnd_145517 := by exact prefixLift 145517
  have htrace : WordTrace (prefixWord ++ tailWord_145517) baseStart_145517 baseEnd_145517 := by
    simpa [prefixWord, tailWord_145517, baseEnd_145517] using wordTrace_append hprefix tailTrace_145517
  have hstable : (prefixWord ++ tailWord_145517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145517).length < 2 ^ (prefixWord ++ tailWord_145517).sum := by decide
  have hdescent : baseEnd_145517 < baseStart_145517 := by decide
  rcases family_descends (prefixWord ++ tailWord_145517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145716 : List Nat := [2, 5, 1, 1, 1, 4, 2, 6]
def baseStart_145716 : Nat := 118140960795 + 145716 * 2 ^ 59
def prefixEnd_145716 : Nat := 4983230072969 + 3 ^ 40 * 145716 * 2
def baseEnd_145716 : Nat := 5542396077826453272583

theorem tailTrace_145716 : CollatzResearch.WordTrace tailWord_145716 prefixEnd_145716 5542396077826453272583 := by
  unfold tailWord_145716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2657349570051646578304501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3543132760068862104406001 2657349570051646578304501)
  ·
    refine ⟨249126522192341866716047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2657349570051646578304501 249126522192341866716047)
    ·
      refine ⟨373689783288512800074071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249126522192341866716047 373689783288512800074071)
      ·
        refine ⟨560534674932769200111107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373689783288512800074071 560534674932769200111107)
        ·
          refine ⟨840802012399153800166661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560534674932769200111107 840802012399153800166661)
          ·
            refine ⟨157650377324841337531249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 840802012399153800166661 157650377324841337531249)
            ·
              refine ⟨118237782993631003148437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157650377324841337531249 118237782993631003148437)
              ·
                refine ⟨5542396077826453272583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118237782993631003148437 5542396077826453272583)
                ·
                  rfl

theorem cell22_145716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 6].length) (baseStart_145716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145716 prefixEnd_145716 := by exact prefixLift 145716
  have htrace : WordTrace (prefixWord ++ tailWord_145716) baseStart_145716 baseEnd_145716 := by
    simpa [prefixWord, tailWord_145716, baseEnd_145716] using wordTrace_append hprefix tailTrace_145716
  have hstable : (prefixWord ++ tailWord_145716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145716).length < 2 ^ (prefixWord ++ tailWord_145716).sum := by decide
  have hdescent : baseEnd_145716 < baseStart_145716 := by decide
  rcases family_descends (prefixWord ++ tailWord_145716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145731 : List Nat := [1, 1, 1, 3, 1, 3, 5, 3, 1, 3]
def baseStart_145731 : Nat := 118140960795 + 145731 * 2 ^ 59
def prefixEnd_145731 : Nat := 4983230072969 + 3 ^ 40 * 145731 * 2
def baseEnd_145731 : Nat := 49886699506983040328201

theorem tailTrace_145731 : CollatzResearch.WordTrace tailWord_145731 prefixEnd_145731 49886699506983040328201 := by
  unfold tailWord_145731
  simp only [CollatzResearch.WordTrace]
  refine ⟨5315246235048950718405047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3543497490032633812270031 5315246235048950718405047)
  ·
    refine ⟨7972869352573426077607571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5315246235048950718405047 7972869352573426077607571)
    ·
      refine ⟨11959304028860139116411357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7972869352573426077607571 11959304028860139116411357)
      ·
        refine ⟨4484739010822552168654259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11959304028860139116411357 4484739010822552168654259)
        ·
          refine ⟨6727108516233828252981389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484739010822552168654259 6727108516233828252981389)
          ·
            refine ⟨2522665693587685594868021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6727108516233828252981389 2522665693587685594868021)
            ·
              refine ⟨236499908773845524518877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2522665693587685594868021 236499908773845524518877)
              ·
                refine ⟨88687465790192071694579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236499908773845524518877 88687465790192071694579)
                ·
                  refine ⟨133031198685288107541869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88687465790192071694579 133031198685288107541869)
                  ·
                    refine ⟨49886699506983040328201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133031198685288107541869 49886699506983040328201)
                    ·
                      rfl

theorem cell22_145731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 3].length) (baseStart_145731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145731 prefixEnd_145731 := by exact prefixLift 145731
  have htrace : WordTrace (prefixWord ++ tailWord_145731) baseStart_145731 baseEnd_145731 := by
    simpa [prefixWord, tailWord_145731, baseEnd_145731] using wordTrace_append hprefix tailTrace_145731
  have hstable : (prefixWord ++ tailWord_145731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145731).length < 2 ^ (prefixWord ++ tailWord_145731).sum := by decide
  have hdescent : baseEnd_145731 < baseStart_145731 := by decide
  rcases family_descends (prefixWord ++ tailWord_145731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145742 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_145742 : Nat := 118140960795 + 145742 * 2 ^ 59
def prefixEnd_145742 : Nat := 4983230072969 + 3 ^ 40 * 145742 * 2
def baseEnd_145742 : Nat := 49890465031782678303167

theorem tailTrace_145742 : CollatzResearch.WordTrace tailWord_145742 prefixEnd_145742 49890465031782678303167 := by
  unfold tailWord_145742
  simp only [CollatzResearch.WordTrace]
  refine ⟨664455929751137449631935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3543764958672733064703653 664455929751137449631935)
  ·
    refine ⟨996683894626706174447903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664455929751137449631935 996683894626706174447903)
    ·
      refine ⟨1495025841940059261671855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 996683894626706174447903 1495025841940059261671855)
      ·
        refine ⟨2242538762910088892507783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1495025841940059261671855 2242538762910088892507783)
        ·
          refine ⟨3363808144365133338761675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242538762910088892507783 3363808144365133338761675)
          ·
            refine ⟨5045712216547700008142513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363808144365133338761675 5045712216547700008142513)
            ·
              refine ⟨3784284162410775006106885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5045712216547700008142513 3784284162410775006106885)
              ·
                refine ⟨709553280452020313645041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3784284162410775006106885 709553280452020313645041)
                ·
                  refine ⟨532164960339015235233781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 709553280452020313645041 532164960339015235233781)
                  ·
                    refine ⟨49890465031782678303167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 532164960339015235233781 49890465031782678303167)
                    ·
                      rfl

theorem cell22_145742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_145742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145742 prefixEnd_145742 := by exact prefixLift 145742
  have htrace : WordTrace (prefixWord ++ tailWord_145742) baseStart_145742 baseEnd_145742 := by
    simpa [prefixWord, tailWord_145742, baseEnd_145742] using wordTrace_append hprefix tailTrace_145742
  have hstable : (prefixWord ++ tailWord_145742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145742).length < 2 ^ (prefixWord ++ tailWord_145742).sum := by decide
  have hdescent : baseEnd_145742 < baseStart_145742 := by decide
  rcases family_descends (prefixWord ++ tailWord_145742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145787 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 3, 5]
def baseStart_145787 : Nat := 118140960795 + 145787 * 2 ^ 59
def prefixEnd_145787 : Nat := 4983230072969 + 3 ^ 40 * 145787 * 2
def baseEnd_145787 : Nat := 49905869451417560928029

theorem tailTrace_145787 : CollatzResearch.WordTrace tailWord_145787 prefixEnd_145787 49905869451417560928029 := by
  unfold tailWord_145787
  simp only [CollatzResearch.WordTrace]
  refine ⟨5317288722846072282443615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3544859148564048188295743 5317288722846072282443615)
  ·
    refine ⟨7975933084269108423665423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5317288722846072282443615 7975933084269108423665423)
    ·
      refine ⟨11963899626403662635498135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7975933084269108423665423 11963899626403662635498135)
      ·
        refine ⟨17945849439605493953247203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11963899626403662635498135 17945849439605493953247203)
        ·
          refine ⟨26918774159408240929870805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17945849439605493953247203 26918774159408240929870805)
          ·
            refine ⟨630908769361130646793847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26918774159408240929870805 630908769361130646793847)
            ·
              refine ⟨946363154041695970190771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630908769361130646793847 946363154041695970190771)
              ·
                refine ⟨1419544731062543955286157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946363154041695970190771 1419544731062543955286157)
                ·
                  refine ⟨532329274148453983232309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1419544731062543955286157 532329274148453983232309)
                  ·
                    refine ⟨49905869451417560928029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 532329274148453983232309 49905869451417560928029)
                    ·
                      rfl

theorem cell22_145787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_145787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145787 prefixEnd_145787 := by exact prefixLift 145787
  have htrace : WordTrace (prefixWord ++ tailWord_145787) baseStart_145787 baseEnd_145787 := by
    simpa [prefixWord, tailWord_145787, baseEnd_145787] using wordTrace_append hprefix tailTrace_145787
  have hstable : (prefixWord ++ tailWord_145787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145787).length < 2 ^ (prefixWord ++ tailWord_145787).sum := by decide
  have hdescent : baseEnd_145787 < baseStart_145787 := by decide
  rcases family_descends (prefixWord ++ tailWord_145787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145821 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_145821 : Nat := 118140960795 + 145821 * 2 ^ 59
def prefixEnd_145821 : Nat := 4983230072969 + 3 ^ 40 * 145821 * 2
def baseEnd_145821 : Nat := 49917508346252805577925

theorem tailTrace_145821 : CollatzResearch.WordTrace tailWord_145821 prefixEnd_145821 49917508346252805577925 := by
  unfold tailWord_145821
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318528804722896089181317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3545685869815264059454211 5318528804722896089181317)
  ·
    refine ⟨997224150885543016721497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5318528804722896089181317 997224150885543016721497)
    ·
      refine ⟨747918113164157262541123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 997224150885543016721497 747918113164157262541123)
      ·
        refine ⟨1121877169746235893811685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747918113164157262541123 1121877169746235893811685)
        ·
          refine ⟨210351969327419230089691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1121877169746235893811685 210351969327419230089691)
          ·
            refine ⟨315527953991128845134537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210351969327419230089691 315527953991128845134537)
            ·
              refine ⟨236645965493346633850903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315527953991128845134537 236645965493346633850903)
              ·
                refine ⟨354968948240019950776355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236645965493346633850903 354968948240019950776355)
                ·
                  refine ⟨532453422360029926164533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354968948240019950776355 532453422360029926164533)
                  ·
                    refine ⟨49917508346252805577925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 532453422360029926164533 49917508346252805577925)
                    ·
                      rfl

theorem cell22_145821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_145821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145821 prefixEnd_145821 := by exact prefixLift 145821
  have htrace : WordTrace (prefixWord ++ tailWord_145821) baseStart_145821 baseEnd_145821 := by
    simpa [prefixWord, tailWord_145821, baseEnd_145821] using wordTrace_append hprefix tailTrace_145821
  have hstable : (prefixWord ++ tailWord_145821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145821).length < 2 ^ (prefixWord ++ tailWord_145821).sum := by decide
  have hdescent : baseEnd_145821 < baseStart_145821 := by decide
  rcases family_descends (prefixWord ++ tailWord_145821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145866 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_145866 : Nat := 118140960795 + 145866 * 2 ^ 59
def prefixEnd_145866 : Nat := 4983230072969 + 3 ^ 40 * 145866 * 2
def baseEnd_145866 : Nat := 49932912765887688202787

theorem tailTrace_145866 : CollatzResearch.WordTrace tailWord_145866 prefixEnd_145866 49932912765887688202787 := by
  unfold tailWord_145866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330042522389967193642363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3546780059706579183046301 1330042522389967193642363)
  ·
    refine ⟨1995063783584950790463545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1330042522389967193642363 1995063783584950790463545)
    ·
      refine ⟨1496297837688713092847659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1995063783584950790463545 1496297837688713092847659)
      ·
        refine ⟨2244446756533069639271489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496297837688713092847659 2244446756533069639271489)
        ·
          refine ⟨1683335067399802229453617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2244446756533069639271489 1683335067399802229453617)
          ·
            refine ⟨1262501300549851672090213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1683335067399802229453617 1262501300549851672090213)
            ·
              refine ⟨236718993853097188516915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1262501300549851672090213 236718993853097188516915)
              ·
                refine ⟨355078490779645782775373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236718993853097188516915 355078490779645782775373)
                ·
                  refine ⟨133154434042367168540765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355078490779645782775373 133154434042367168540765)
                  ·
                    refine ⟨49932912765887688202787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133154434042367168540765 49932912765887688202787)
                    ·
                      rfl

theorem cell22_145866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_145866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145866 prefixEnd_145866 := by exact prefixLift 145866
  have htrace : WordTrace (prefixWord ++ tailWord_145866) baseStart_145866 baseEnd_145866 := by
    simpa [prefixWord, tailWord_145866, baseEnd_145866] using wordTrace_append hprefix tailTrace_145866
  have hstable : (prefixWord ++ tailWord_145866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145866).length < 2 ^ (prefixWord ++ tailWord_145866).sum := by decide
  have hdescent : baseEnd_145866 < baseStart_145866 := by decide
  rcases family_descends (prefixWord ++ tailWord_145866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145939 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 1, 5]
def baseStart_145939 : Nat := 118140960795 + 145939 * 2 ^ 59
def prefixEnd_145939 : Nat := 4983230072969 + 3 ^ 40 * 145939 * 2
def baseEnd_145939 : Nat := 49957902157739831127563

theorem tailTrace_145939 : CollatzResearch.WordTrace tailWord_145939 prefixEnd_145939 49957902157739831127563 := by
  unfold tailWord_145939
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322832618295402241976871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3548555078863601494651247 5322832618295402241976871)
  ·
    refine ⟨7984248927443103362965307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5322832618295402241976871 7984248927443103362965307)
    ·
      refine ⟨11976373391164655044447961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7984248927443103362965307 11976373391164655044447961)
      ·
        refine ⟨8982280043373491283335971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11976373391164655044447961 8982280043373491283335971)
        ·
          refine ⟨13473420065060236925003957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8982280043373491283335971 13473420065060236925003957)
          ·
            refine ⟨1263133131099397211719121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13473420065060236925003957 1263133131099397211719121)
            ·
              refine ⟨947349848324547908789341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263133131099397211719121 947349848324547908789341)
              ·
                refine ⟨355256193121705465796003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947349848324547908789341 355256193121705465796003)
                ·
                  refine ⟨532884289682558198694005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355256193121705465796003 532884289682558198694005)
                  ·
                    refine ⟨49957902157739831127563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 532884289682558198694005 49957902157739831127563)
                    ·
                      rfl

theorem cell22_145939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_145939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145939 prefixEnd_145939 := by exact prefixLift 145939
  have htrace : WordTrace (prefixWord ++ tailWord_145939) baseStart_145939 baseEnd_145939 := by
    simpa [prefixWord, tailWord_145939, baseEnd_145939] using wordTrace_append hprefix tailTrace_145939
  have hstable : (prefixWord ++ tailWord_145939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145939).length < 2 ^ (prefixWord ++ tailWord_145939).sum := by decide
  have hdescent : baseEnd_145939 < baseStart_145939 := by decide
  rcases family_descends (prefixWord ++ tailWord_145939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145943 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 3, 4]
def baseStart_145943 : Nat := 118140960795 + 145943 * 2 ^ 59
def prefixEnd_145943 : Nat := 4983230072969 + 3 ^ 40 * 145943 * 2
def baseEnd_145943 : Nat := 49959271439485154027551

theorem tailTrace_145943 : CollatzResearch.WordTrace tailWord_145943 prefixEnd_145943 49959271439485154027551 := by
  unfold tailWord_145943
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322978510280910925122483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3548652340187273950081655 5322978510280910925122483)
  ·
    refine ⟨7984467765421366387683725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5322978510280910925122483 7984467765421366387683725)
    ·
      refine ⟨2994175412033012395381397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7984467765421366387683725 2994175412033012395381397)
      ·
        refine ⟨140351972439047456033503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2994175412033012395381397 140351972439047456033503)
        ·
          refine ⟨210527958658571184050255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140351972439047456033503 210527958658571184050255)
          ·
            refine ⟨315791937987856776075383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210527958658571184050255 315791937987856776075383)
            ·
              refine ⟨473687906981785164113075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315791937987856776075383 473687906981785164113075)
              ·
                refine ⟨710531860472677746169613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473687906981785164113075 710531860472677746169613)
                ·
                  refine ⟨266449447677254154813605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710531860472677746169613 266449447677254154813605)
                  ·
                    refine ⟨49959271439485154027551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 266449447677254154813605 49959271439485154027551)
                    ·
                      rfl

theorem cell22_145943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_145943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145943 prefixEnd_145943 := by exact prefixLift 145943
  have htrace : WordTrace (prefixWord ++ tailWord_145943) baseStart_145943 baseEnd_145943 := by
    simpa [prefixWord, tailWord_145943, baseEnd_145943] using wordTrace_append hprefix tailTrace_145943
  have hstable : (prefixWord ++ tailWord_145943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145943).length < 2 ^ (prefixWord ++ tailWord_145943).sum := by decide
  have hdescent : baseEnd_145943 < baseStart_145943 := by decide
  rcases family_descends (prefixWord ++ tailWord_145943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145960 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 1, 4]
def baseStart_145960 : Nat := 118140960795 + 145960 * 2 ^ 59
def prefixEnd_145960 : Nat := 4983230072969 + 3 ^ 40 * 145960 * 2
def baseEnd_145960 : Nat := 49965090886902776352499

theorem tailTrace_145960 : CollatzResearch.WordTrace tailWord_145960 prefixEnd_145960 49965090886902776352499 := by
  unfold tailWord_145960
  simp only [CollatzResearch.WordTrace]
  refine ⟨2661799275609661414245667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3549065700812881885660889 2661799275609661414245667)
  ·
    refine ⟨3992698913414492121368501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2661799275609661414245667 3992698913414492121368501)
    ·
      refine ⟨374315523132608636378297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3992698913414492121368501 374315523132608636378297)
      ·
        refine ⟨280736642349456477283723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374315523132608636378297 280736642349456477283723)
        ·
          refine ⟨421104963524184715925585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280736642349456477283723 421104963524184715925585)
          ·
            refine ⟨315828722643138536944189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421104963524184715925585 315828722643138536944189)
            ·
              refine ⟨118435770991176951354071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 315828722643138536944189 118435770991176951354071)
              ·
                refine ⟨177653656486765427031107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118435770991176951354071 177653656486765427031107)
                ·
                  refine ⟨266480484730148140546661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177653656486765427031107 266480484730148140546661)
                  ·
                    refine ⟨49965090886902776352499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 266480484730148140546661 49965090886902776352499)
                    ·
                      rfl

theorem cell22_145960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_145960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145960 prefixEnd_145960 := by exact prefixLift 145960
  have htrace : WordTrace (prefixWord ++ tailWord_145960) baseStart_145960 baseEnd_145960 := by
    simpa [prefixWord, tailWord_145960, baseEnd_145960] using wordTrace_append hprefix tailTrace_145960
  have hstable : (prefixWord ++ tailWord_145960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145960).length < 2 ^ (prefixWord ++ tailWord_145960).sum := by decide
  have hdescent : baseEnd_145960 < baseStart_145960 := by decide
  rcases family_descends (prefixWord ++ tailWord_145960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145973 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_145973 : Nat := 118140960795 + 145973 * 2 ^ 59
def prefixEnd_145973 : Nat := 4983230072969 + 3 ^ 40 * 145973 * 2
def baseEnd_145973 : Nat := 49969541052575075777459

theorem tailTrace_145973 : CollatzResearch.WordTrace tailWord_145973 prefixEnd_145973 49969541052575075777459 := by
  unfold tailWord_145973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324072700172226048714573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3549381800114817365809715 5324072700172226048714573)
  ·
    refine ⟨1996527262564584768267965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5324072700172226048714573 1996527262564584768267965)
    ·
      refine ⟨748697723461719288100487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1996527262564584768267965 748697723461719288100487)
      ·
        refine ⟨1123046585192578932150731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748697723461719288100487 1123046585192578932150731)
        ·
          refine ⟨1684569877788868398226097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123046585192578932150731 1684569877788868398226097)
          ·
            refine ⟨1263427408341651298669573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684569877788868398226097 1263427408341651298669573)
            ·
              refine ⟨236892639064059618500545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1263427408341651298669573 236892639064059618500545)
              ·
                refine ⟨177669479298044713875409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236892639064059618500545 177669479298044713875409)
                ·
                  refine ⟨133252109473533535406557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177669479298044713875409 133252109473533535406557)
                  ·
                    refine ⟨49969541052575075777459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133252109473533535406557 49969541052575075777459)
                    ·
                      rfl

theorem cell22_145973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_145973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145973 prefixEnd_145973 := by exact prefixLift 145973
  have htrace : WordTrace (prefixWord ++ tailWord_145973) baseStart_145973 baseEnd_145973 := by
    simpa [prefixWord, tailWord_145973, baseEnd_145973] using wordTrace_append hprefix tailTrace_145973
  have hstable : (prefixWord ++ tailWord_145973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145973).length < 2 ^ (prefixWord ++ tailWord_145973).sum := by decide
  have hdescent : baseEnd_145973 < baseStart_145973 := by decide
  rcases family_descends (prefixWord ++ tailWord_145973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145990 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_145990 : Nat := 118140960795 + 145990 * 2 ^ 59
def prefixEnd_145990 : Nat := 4983230072969 + 3 ^ 40 * 145990 * 2
def baseEnd_145990 : Nat := 49975360499992698102407

theorem tailTrace_145990 : CollatzResearch.WordTrace tailWord_145990 prefixEnd_145990 49975360499992698102407 := by
  unfold tailWord_145990
  simp only [CollatzResearch.WordTrace]
  refine ⟨166396648159707436002607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3549795160740425301388949 166396648159707436002607)
  ·
    refine ⟨249594972239561154003911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166396648159707436002607 249594972239561154003911)
    ·
      refine ⟨374392458359341731005867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249594972239561154003911 374392458359341731005867)
      ·
        refine ⟨561588687539012596508801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374392458359341731005867 561588687539012596508801)
        ·
          refine ⟨421191515654259447381601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561588687539012596508801 421191515654259447381601)
          ·
            refine ⟨315893636740694585536201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421191515654259447381601 315893636740694585536201)
            ·
              refine ⟨236920227555520939152151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315893636740694585536201 236920227555520939152151)
              ·
                refine ⟨355380341333281408728227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236920227555520939152151 355380341333281408728227)
                ·
                  refine ⟨533070511999922113092341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355380341333281408728227 533070511999922113092341)
                  ·
                    refine ⟨49975360499992698102407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 533070511999922113092341 49975360499992698102407)
                    ·
                      rfl

theorem cell22_145990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_145990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_145990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_145990 prefixEnd_145990 := by exact prefixLift 145990
  have htrace : WordTrace (prefixWord ++ tailWord_145990) baseStart_145990 baseEnd_145990 := by
    simpa [prefixWord, tailWord_145990, baseEnd_145990] using wordTrace_append hprefix tailTrace_145990
  have hstable : (prefixWord ++ tailWord_145990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145990).length < 2 ^ (prefixWord ++ tailWord_145990).sum := by decide
  have hdescent : baseEnd_145990 < baseStart_145990 := by decide
  rcases family_descends (prefixWord ++ tailWord_145990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146001 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 5, 3]
def baseStart_146001 : Nat := 118140960795 + 146001 * 2 ^ 59
def prefixEnd_146001 : Nat := 4983230072969 + 3 ^ 40 * 146001 * 2
def baseEnd_146001 : Nat := 49979126024792336077373

theorem tailTrace_146001 : CollatzResearch.WordTrace tailWord_146001 prefixEnd_146001 49979126024792336077373 := by
  unfold tailWord_146001
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325093944070786830733857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3550062629380524553822571 5325093944070786830733857)
  ·
    refine ⟨3993820458053090123050393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5325093944070786830733857 3993820458053090123050393)
    ·
      refine ⟨2995365343539817592287795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3993820458053090123050393 2995365343539817592287795)
      ·
        refine ⟨4493048015309726388431693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995365343539817592287795 4493048015309726388431693)
        ·
          refine ⟨1684893005741147395661885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4493048015309726388431693 1684893005741147395661885)
          ·
            refine ⟨631834877152930273373207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1684893005741147395661885 631834877152930273373207)
            ·
              refine ⟨947752315729395410059811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631834877152930273373207 947752315729395410059811)
              ·
                refine ⟨1421628473594093115089717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947752315729395410059811 1421628473594093115089717)
                ·
                  refine ⟨133277669399446229539661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1421628473594093115089717 133277669399446229539661)
                  ·
                    refine ⟨49979126024792336077373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133277669399446229539661 49979126024792336077373)
                    ·
                      rfl

theorem cell22_146001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_146001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146001 prefixEnd_146001 := by exact prefixLift 146001
  have htrace : WordTrace (prefixWord ++ tailWord_146001) baseStart_146001 baseEnd_146001 := by
    simpa [prefixWord, tailWord_146001, baseEnd_146001] using wordTrace_append hprefix tailTrace_146001
  have hstable : (prefixWord ++ tailWord_146001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146001).length < 2 ^ (prefixWord ++ tailWord_146001).sum := by decide
  have hdescent : baseEnd_146001 < baseStart_146001 := by decide
  rcases family_descends (prefixWord ++ tailWord_146001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146031 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 5]
def baseStart_146031 : Nat := 118140960795 + 146031 * 2 ^ 59
def prefixEnd_146031 : Nat := 4983230072969 + 3 ^ 40 * 146031 * 2
def baseEnd_146031 : Nat := 16663131879294085942427

theorem tailTrace_146031 : CollatzResearch.WordTrace tailWord_146031 prefixEnd_146031 16663131879294085942427 := by
  unfold tailWord_146031
  simp only [CollatzResearch.WordTrace]
  refine ⟨5326188133962101954325947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3550792089308067969550631 5326188133962101954325947)
  ·
    refine ⟨7989282200943152931488921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5326188133962101954325947 7989282200943152931488921)
    ·
      refine ⟨5991961650707364698616691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7989282200943152931488921 5991961650707364698616691)
      ·
        refine ⟨8987942476061047047925037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991961650707364698616691 8987942476061047047925037)
        ·
          refine ⟨3370478428522892642971889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8987942476061047047925037 3370478428522892642971889)
          ·
            refine ⟨2527858821392169482228917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3370478428522892642971889 2527858821392169482228917)
            ·
              refine ⟨236986764505515888958961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2527858821392169482228917 236986764505515888958961)
              ·
                refine ⟨177740073379136916719221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236986764505515888958961 177740073379136916719221)
                ·
                  refine ⟨16663131879294085942427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177740073379136916719221 16663131879294085942427)
                  ·
                    rfl

theorem cell22_146031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 5].length) (baseStart_146031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146031 prefixEnd_146031 := by exact prefixLift 146031
  have htrace : WordTrace (prefixWord ++ tailWord_146031) baseStart_146031 baseEnd_146031 := by
    simpa [prefixWord, tailWord_146031, baseEnd_146031] using wordTrace_append hprefix tailTrace_146031
  have hstable : (prefixWord ++ tailWord_146031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146031).length < 2 ^ (prefixWord ++ tailWord_146031).sum := by decide
  have hdescent : baseEnd_146031 < baseStart_146031 := by decide
  rcases family_descends (prefixWord ++ tailWord_146031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146048 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 5]
def baseStart_146048 : Nat := 118140960795 + 146048 * 2 ^ 59
def prefixEnd_146048 : Nat := 4983230072969 + 3 ^ 40 * 146048 * 2
def baseEnd_146048 : Nat := 16665071695099960050743

theorem tailTrace_146048 : CollatzResearch.WordTrace tailWord_146048 prefixEnd_146048 16665071695099960050743 := by
  unfold tailWord_146048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663404087450256928847399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3551205449933675905129865 2663404087450256928847399)
  ·
    refine ⟨3995106131175385393271099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663404087450256928847399 3995106131175385393271099)
    ·
      refine ⟨5992659196763078089906649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995106131175385393271099 5992659196763078089906649)
      ·
        refine ⟨4494494397572308567429987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5992659196763078089906649 4494494397572308567429987)
        ·
          refine ⟨6741741596358462851144981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4494494397572308567429987 6741741596358462851144981)
          ·
            refine ⟨316019137329302946147421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6741741596358462851144981 316019137329302946147421)
            ·
              refine ⟨118507176498488604805283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316019137329302946147421 118507176498488604805283)
              ·
                refine ⟨177760764747732907207925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118507176498488604805283 177760764747732907207925)
                ·
                  refine ⟨16665071695099960050743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177760764747732907207925 16665071695099960050743)
                  ·
                    rfl

theorem cell22_146048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_146048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146048 prefixEnd_146048 := by exact prefixLift 146048
  have htrace : WordTrace (prefixWord ++ tailWord_146048) baseStart_146048 baseEnd_146048 := by
    simpa [prefixWord, tailWord_146048, baseEnd_146048] using wordTrace_append hprefix tailTrace_146048
  have hstable : (prefixWord ++ tailWord_146048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146048).length < 2 ^ (prefixWord ++ tailWord_146048).sum := by decide
  have hdescent : baseEnd_146048 < baseStart_146048 := by decide
  rcases family_descends (prefixWord ++ tailWord_146048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146059 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 8]
def baseStart_146059 : Nat := 118140960795 + 146059 * 2 ^ 59
def prefixEnd_146059 : Nat := 4983230072969 + 3 ^ 40 * 146059 * 2
def baseEnd_146059 : Nat := 16666326870033172709065

theorem tailTrace_146059 : CollatzResearch.WordTrace tailWord_146059 prefixEnd_146059 16666326870033172709065 := by
  unfold tailWord_146059
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327209377860662736345231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3551472918573775157563487 5327209377860662736345231)
  ·
    refine ⟨7990814066790994104517847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5327209377860662736345231 7990814066790994104517847)
    ·
      refine ⟨11986221100186491156776771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7990814066790994104517847 11986221100186491156776771)
      ·
        refine ⟨17979331650279736735165157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11986221100186491156776771 17979331650279736735165157)
        ·
          refine ⟨3371124684427450637843467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17979331650279736735165157 3371124684427450637843467)
          ·
            refine ⟨5056687026641175956765201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371124684427450637843467 5056687026641175956765201)
            ·
              refine ⟨3792515269980881967573901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5056687026641175956765201 3792515269980881967573901)
              ·
                refine ⟨1422193226242830737840213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3792515269980881967573901 1422193226242830737840213)
                ·
                  refine ⟨16666326870033172709065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1422193226242830737840213 16666326870033172709065)
                  ·
                    rfl

theorem cell22_146059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_146059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146059 prefixEnd_146059 := by exact prefixLift 146059
  have htrace : WordTrace (prefixWord ++ tailWord_146059) baseStart_146059 baseEnd_146059 := by
    simpa [prefixWord, tailWord_146059, baseEnd_146059] using wordTrace_append hprefix tailTrace_146059
  have hstable : (prefixWord ++ tailWord_146059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146059).length < 2 ^ (prefixWord ++ tailWord_146059).sum := by decide
  have hdescent : baseEnd_146059 < baseStart_146059 := by decide
  rcases family_descends (prefixWord ++ tailWord_146059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146093 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 6]
def baseStart_146093 : Nat := 118140960795 + 146093 * 2 ^ 59
def prefixEnd_146093 : Nat := 4983230072969 + 3 ^ 40 * 146093 * 2
def baseEnd_146093 : Nat := 16670206501644920925697

theorem tailTrace_146093 : CollatzResearch.WordTrace tailWord_146093 prefixEnd_146093 16670206501644920925697 := by
  unfold tailWord_146093
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328449459737486543082933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3552299639824991028721955 5328449459737486543082933)
  ·
    refine ⟨499542136850389363414025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5328449459737486543082933 499542136850389363414025)
    ·
      refine ⟨374656602637792022560519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 499542136850389363414025 374656602637792022560519)
      ·
        refine ⟨561984903956688033840779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374656602637792022560519 561984903956688033840779)
        ·
          refine ⟨842977355935032050761169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561984903956688033840779 842977355935032050761169)
          ·
            refine ⟨632233016951274038070877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842977355935032050761169 632233016951274038070877)
            ·
              refine ⟨237087381356727764276579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 632233016951274038070877 237087381356727764276579)
              ·
                refine ⟨355631072035091646414869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237087381356727764276579 355631072035091646414869)
                ·
                  refine ⟨16670206501644920925697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 355631072035091646414869 16670206501644920925697)
                  ·
                    rfl

theorem cell22_146093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_146093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146093 prefixEnd_146093 := by exact prefixLift 146093
  have htrace : WordTrace (prefixWord ++ tailWord_146093) baseStart_146093 baseEnd_146093 := by
    simpa [prefixWord, tailWord_146093, baseEnd_146093] using wordTrace_append hprefix tailTrace_146093
  have hstable : (prefixWord ++ tailWord_146093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146093).length < 2 ^ (prefixWord ++ tailWord_146093).sum := by decide
  have hdescent : baseEnd_146093 < baseStart_146093 := by decide
  rcases family_descends (prefixWord ++ tailWord_146093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146106 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_146106 : Nat := 118140960795 + 146106 * 2 ^ 59
def prefixEnd_146106 : Nat := 4983230072969 + 3 ^ 40 * 146106 * 2
def baseEnd_146106 : Nat := 50015069670607062202051

theorem tailTrace_146106 : CollatzResearch.WordTrace tailWord_146106 prefixEnd_146106 50015069670607062202051 := by
  unfold tailWord_146106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1332230902172597440826543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3552615739126926508870781 1332230902172597440826543)
  ·
    refine ⟨1998346353258896161239815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1332230902172597440826543 1998346353258896161239815)
    ·
      refine ⟨2997519529888344241859723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1998346353258896161239815 2997519529888344241859723)
      ·
        refine ⟨4496279294832516362789585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997519529888344241859723 4496279294832516362789585)
        ·
          refine ⟨3372209471124387272092189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4496279294832516362789585 3372209471124387272092189)
          ·
            refine ⟨1264578551671645227034571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3372209471124387272092189 1264578551671645227034571)
            ·
              refine ⟨1896867827507467840551857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264578551671645227034571 1896867827507467840551857)
              ·
                refine ⟨1422650870630600880413893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896867827507467840551857 1422650870630600880413893)
                ·
                  refine ⟨266747038243237665077605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422650870630600880413893 266747038243237665077605)
                  ·
                    refine ⟨50015069670607062202051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 266747038243237665077605 50015069670607062202051)
                    ·
                      rfl

theorem cell22_146106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_146106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146106 prefixEnd_146106 := by exact prefixLift 146106
  have htrace : WordTrace (prefixWord ++ tailWord_146106) baseStart_146106 baseEnd_146106 := by
    simpa [prefixWord, tailWord_146106, baseEnd_146106] using wordTrace_append hprefix tailTrace_146106
  have hstable : (prefixWord ++ tailWord_146106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146106).length < 2 ^ (prefixWord ++ tailWord_146106).sum := by decide
  have hdescent : baseEnd_146106 < baseStart_146106 := by decide
  rcases family_descends (prefixWord ++ tailWord_146106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146140 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_146140 : Nat := 118140960795 + 146140 * 2 ^ 59
def prefixEnd_146140 : Nat := 4983230072969 + 3 ^ 40 * 146140 * 2
def baseEnd_146140 : Nat := 50026708565442306851947

theorem tailTrace_146140 : CollatzResearch.WordTrace tailWord_146140 prefixEnd_146140 50026708565442306851947 := by
  unfold tailWord_146140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665081845283606785021937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3553442460378142380029249 2665081845283606785021937)
  ·
    refine ⟨1998811383962705088766453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2665081845283606785021937 1998811383962705088766453)
    ·
      refine ⟨187388567246503602071855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1998811383962705088766453 187388567246503602071855)
      ·
        refine ⟨281082850869755403107783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187388567246503602071855 281082850869755403107783)
        ·
          refine ⟨421624276304633104661675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281082850869755403107783 421624276304633104661675)
          ·
            refine ⟨632436414456949656992513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421624276304633104661675 632436414456949656992513)
            ·
              refine ⟨474327310842712242744385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632436414456949656992513 474327310842712242744385)
              ·
                refine ⟨355745483132034182058289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474327310842712242744385 355745483132034182058289)
                ·
                  refine ⟨266809112349025636543717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355745483132034182058289 266809112349025636543717)
                  ·
                    refine ⟨50026708565442306851947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 266809112349025636543717 50026708565442306851947)
                    ·
                      rfl

theorem cell22_146140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_146140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146140 prefixEnd_146140 := by exact prefixLift 146140
  have htrace : WordTrace (prefixWord ++ tailWord_146140) baseStart_146140 baseEnd_146140 := by
    simpa [prefixWord, tailWord_146140, baseEnd_146140] using wordTrace_append hprefix tailTrace_146140
  have hstable : (prefixWord ++ tailWord_146140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146140).length < 2 ^ (prefixWord ++ tailWord_146140).sum := by decide
  have hdescent : baseEnd_146140 < baseStart_146140 := by decide
  rcases family_descends (prefixWord ++ tailWord_146140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146243 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 6, 3]
def baseStart_146243 : Nat := 118140960795 + 146243 * 2 ^ 59
def prefixEnd_146243 : Nat := 4983230072969 + 3 ^ 40 * 146243 * 2
def baseEnd_146243 : Nat := 50061967570384371526631

theorem tailTrace_146243 : CollatzResearch.WordTrace tailWord_146243 prefixEnd_146243 50061967570384371526631 := by
  unfold tailWord_146243
  simp only [CollatzResearch.WordTrace]
  refine ⟨5333920409194062161043383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3555946939462708107362255 5333920409194062161043383)
  ·
    refine ⟨8000880613791093241565075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5333920409194062161043383 8000880613791093241565075)
    ·
      refine ⟨12001320920686639862347613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8000880613791093241565075 12001320920686639862347613)
      ·
        refine ⟨4500495345257489948380355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12001320920686639862347613 4500495345257489948380355)
        ·
          refine ⟨6750743017886234922570533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500495345257489948380355 6750743017886234922570533)
          ·
            refine ⟨1265764315853669047981975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6750743017886234922570533 1265764315853669047981975)
            ·
              refine ⟨1898646473780503571972963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265764315853669047981975 1898646473780503571972963)
              ·
                refine ⟨2847969710670755357959445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898646473780503571972963 2847969710670755357959445)
                ·
                  refine ⟨133498580187691657404349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2847969710670755357959445 133498580187691657404349)
                  ·
                    refine ⟨50061967570384371526631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133498580187691657404349 50061967570384371526631)
                    ·
                      rfl

theorem cell22_146243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 3].length) (baseStart_146243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146243 prefixEnd_146243 := by exact prefixLift 146243
  have htrace : WordTrace (prefixWord ++ tailWord_146243) baseStart_146243 baseEnd_146243 := by
    simpa [prefixWord, tailWord_146243, baseEnd_146243] using wordTrace_append hprefix tailTrace_146243
  have hstable : (prefixWord ++ tailWord_146243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146243).length < 2 ^ (prefixWord ++ tailWord_146243).sum := by decide
  have hdescent : baseEnd_146243 < baseStart_146243 := by decide
  rcases family_descends (prefixWord ++ tailWord_146243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146256 : List Nat := [2, 1, 1, 1, 1, 4, 12]
def baseStart_146256 : Nat := 118140960795 + 146256 * 2 ^ 59
def prefixEnd_146256 : Nat := 4983230072969 + 3 ^ 40 * 146256 * 2
def baseEnd_146256 : Nat := 1854311768002098924133

theorem tailTrace_146256 : CollatzResearch.WordTrace tailWord_146256 prefixEnd_146256 1854311768002098924133 := by
  unfold tailWord_146256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667197279073482690633311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3556263038764643587511081 2667197279073482690633311)
  ·
    refine ⟨4000795918610224035949967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2667197279073482690633311 4000795918610224035949967)
    ·
      refine ⟨6001193877915336053924951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4000795918610224035949967 6001193877915336053924951)
      ·
        refine ⟨9001790816873004080887427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6001193877915336053924951 9001790816873004080887427)
        ·
          refine ⟨13502686225309506121331141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9001790816873004080887427 13502686225309506121331141)
          ·
            refine ⟨2531753667245532397749589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13502686225309506121331141 2531753667245532397749589)
            ·
              refine ⟨1854311768002098924133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 2531753667245532397749589 1854311768002098924133)
              ·
                rfl

theorem cell22_146256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 12].length) (baseStart_146256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146256 prefixEnd_146256 := by exact prefixLift 146256
  have htrace : WordTrace (prefixWord ++ tailWord_146256) baseStart_146256 baseEnd_146256 := by
    simpa [prefixWord, tailWord_146256, baseEnd_146256] using wordTrace_append hprefix tailTrace_146256
  have hstable : (prefixWord ++ tailWord_146256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146256).length < 2 ^ (prefixWord ++ tailWord_146256).sum := by decide
  have hdescent : baseEnd_146256 < baseStart_146256 := by decide
  rcases family_descends (prefixWord ++ tailWord_146256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146277 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_146277 : Nat := 118140960795 + 146277 * 2 ^ 59
def prefixEnd_146277 : Nat := 4983230072969 + 3 ^ 40 * 146277 * 2
def baseEnd_146277 : Nat := 50073606465219616176527

theorem tailTrace_146277 : CollatzResearch.WordTrace tailWord_146277 prefixEnd_146277 50073606465219616176527 := by
  unfold tailWord_146277
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335160491070885967781085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3556773660713923978520723 5335160491070885967781085)
  ·
    refine ⟨2000685184151582237917907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5335160491070885967781085 2000685184151582237917907)
    ·
      refine ⟨3001027776227373356876861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2000685184151582237917907 3001027776227373356876861)
      ·
        refine ⟨1125385416085265008828823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3001027776227373356876861 1125385416085265008828823)
        ·
          refine ⟨1688078124127897513243235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125385416085265008828823 1688078124127897513243235)
          ·
            refine ⟨2532117186191846269864853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688078124127897513243235 2532117186191846269864853)
            ·
              refine ⟨118692993102742793899915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2532117186191846269864853 118692993102742793899915)
              ·
                refine ⟨178039489654114190849873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118692993102742793899915 178039489654114190849873)
                ·
                  refine ⟨133529617240585643137405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178039489654114190849873 133529617240585643137405)
                  ·
                    refine ⟨50073606465219616176527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133529617240585643137405 50073606465219616176527)
                    ·
                      rfl

theorem cell22_146277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_146277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146277 prefixEnd_146277 := by exact prefixLift 146277
  have htrace : WordTrace (prefixWord ++ tailWord_146277) baseStart_146277 baseEnd_146277 := by
    simpa [prefixWord, tailWord_146277, baseEnd_146277] using wordTrace_append hprefix tailTrace_146277
  have hstable : (prefixWord ++ tailWord_146277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146277).length < 2 ^ (prefixWord ++ tailWord_146277).sum := by decide
  have hdescent : baseEnd_146277 < baseStart_146277 := by decide
  rcases family_descends (prefixWord ++ tailWord_146277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146335 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 5]
def baseStart_146335 : Nat := 118140960795 + 146335 * 2 ^ 59
def prefixEnd_146335 : Nat := 4983230072969 + 3 ^ 40 * 146335 * 2
def baseEnd_146335 : Nat := 16697820350175599408783

theorem tailTrace_146335 : CollatzResearch.WordTrace tailWord_146335 prefixEnd_146335 16697820350175599408783 := by
  unfold tailWord_146335
  simp only [CollatzResearch.WordTrace]
  refine ⟨5337275924860761873392459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3558183949907174582261639 5337275924860761873392459)
  ·
    refine ⟨8005913887291142810088689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5337275924860761873392459 8005913887291142810088689)
    ·
      refine ⟨6004435415468357107566517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8005913887291142810088689 6004435415468357107566517)
      ·
        refine ⟨562915820200158478834361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6004435415468357107566517 562915820200158478834361)
        ·
          refine ⟨422186865150118859125771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562915820200158478834361 422186865150118859125771)
          ·
            refine ⟨633280297725178288688657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422186865150118859125771 633280297725178288688657)
            ·
              refine ⟨474960223293883716516493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633280297725178288688657 474960223293883716516493)
              ·
                refine ⟨178110083735206393693685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 474960223293883716516493 178110083735206393693685)
                ·
                  refine ⟨16697820350175599408783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178110083735206393693685 16697820350175599408783)
                  ·
                    rfl

theorem cell22_146335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 5].length) (baseStart_146335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146335 prefixEnd_146335 := by exact prefixLift 146335
  have htrace : WordTrace (prefixWord ++ tailWord_146335) baseStart_146335 baseEnd_146335 := by
    simpa [prefixWord, tailWord_146335, baseEnd_146335] using wordTrace_append hprefix tailTrace_146335
  have hstable : (prefixWord ++ tailWord_146335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146335).length < 2 ^ (prefixWord ++ tailWord_146335).sum := by decide
  have hdescent : baseEnd_146335 < baseStart_146335 := by decide
  rcases family_descends (prefixWord ++ tailWord_146335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146356 : List Nat := [2, 5, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_146356 : Nat := 118140960795 + 146356 * 2 ^ 59
def prefixEnd_146356 : Nat := 4983230072969 + 3 ^ 40 * 146356 * 2
def baseEnd_146356 : Nat := 50100649779689743451285

theorem tailTrace_146356 : CollatzResearch.WordTrace tailWord_146356 prefixEnd_146356 50100649779689743451285 := by
  unfold tailWord_146356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669020928892341229953461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3558694571856454973271281 2669020928892341229953461)
  ·
    refine ⟨250220712083656990308137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2669020928892341229953461 250220712083656990308137)
    ·
      refine ⟨187665534062742742731103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250220712083656990308137 187665534062742742731103)
      ·
        refine ⟨281498301094114114096655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187665534062742742731103 281498301094114114096655)
        ·
          refine ⟨422247451641171171144983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281498301094114114096655 422247451641171171144983)
          ·
            refine ⟨633371177461756756717475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422247451641171171144983 633371177461756756717475)
            ·
              refine ⟨950056766192635135076213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633371177461756756717475 950056766192635135076213)
              ·
                refine ⟨89067821830559543913395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 950056766192635135076213 89067821830559543913395)
                ·
                  refine ⟨133601732745839315870093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89067821830559543913395 133601732745839315870093)
                  ·
                    refine ⟨50100649779689743451285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133601732745839315870093 50100649779689743451285)
                    ·
                      rfl

theorem cell22_146356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_146356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146356 prefixEnd_146356 := by exact prefixLift 146356
  have htrace : WordTrace (prefixWord ++ tailWord_146356) baseStart_146356 baseEnd_146356 := by
    simpa [prefixWord, tailWord_146356, baseEnd_146356] using wordTrace_append hprefix tailTrace_146356
  have hstable : (prefixWord ++ tailWord_146356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146356).length < 2 ^ (prefixWord ++ tailWord_146356).sum := by decide
  have hdescent : baseEnd_146356 < baseStart_146356 := by decide
  rcases family_descends (prefixWord ++ tailWord_146356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146380 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 6]
def baseStart_146380 : Nat := 118140960795 + 146380 * 2 ^ 59
def prefixEnd_146380 : Nat := 4983230072969 + 3 ^ 40 * 146380 * 2
def baseEnd_146380 : Nat := 16702955156720560283737

theorem tailTrace_146380 : CollatzResearch.WordTrace tailWord_146380 prefixEnd_146380 16702955156720560283737 := by
  unfold tailWord_146380
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669458604848867279390297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3559278139798489705853729 2669458604848867279390297)
  ·
    refine ⟨2002093953636650459542723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2669458604848867279390297 2002093953636650459542723)
    ·
      refine ⟨3003140930454975689314085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2002093953636650459542723 3003140930454975689314085)
      ·
        refine ⟨563088924460307941746391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3003140930454975689314085 563088924460307941746391)
        ·
          refine ⟨844633386690461912619587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563088924460307941746391 844633386690461912619587)
          ·
            refine ⟨1266950080035692868929381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844633386690461912619587 1266950080035692868929381)
            ·
              refine ⟨237553140006692412924259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1266950080035692868929381 237553140006692412924259)
              ·
                refine ⟨356329710010038619386389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237553140006692412924259 356329710010038619386389)
                ·
                  refine ⟨16702955156720560283737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 356329710010038619386389 16702955156720560283737)
                  ·
                    rfl

theorem cell22_146380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_146380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146380 prefixEnd_146380 := by exact prefixLift 146380
  have htrace : WordTrace (prefixWord ++ tailWord_146380) baseStart_146380 baseEnd_146380 := by
    simpa [prefixWord, tailWord_146380, baseEnd_146380] using wordTrace_append hprefix tailTrace_146380
  have hstable : (prefixWord ++ tailWord_146380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146380).length < 2 ^ (prefixWord ++ tailWord_146380).sum := by decide
  have hdescent : baseEnd_146380 < baseStart_146380 := by decide
  rcases family_descends (prefixWord ++ tailWord_146380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146410 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_146410 : Nat := 118140960795 + 146410 * 2 ^ 59
def prefixEnd_146410 : Nat := 4983230072969 + 3 ^ 40 * 146410 * 2
def baseEnd_146410 : Nat := 50119135083251602601119

theorem tailTrace_146410 : CollatzResearch.WordTrace tailWord_146410 prefixEnd_146410 50119135083251602601119 := by
  unfold tailWord_146410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335002849897262420593171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3560007599726033121581789 1335002849897262420593171)
  ·
    refine ⟨2002504274845893630889757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1335002849897262420593171 2002504274845893630889757)
    ·
      refine ⟨750939103067210111583659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2002504274845893630889757 750939103067210111583659)
      ·
        refine ⟨1126408654600815167375489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750939103067210111583659 1126408654600815167375489)
        ·
          refine ⟨844806490950611375531617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126408654600815167375489 844806490950611375531617)
          ·
            refine ⟨633604868212958531648713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844806490950611375531617 633604868212958531648713)
            ·
              refine ⟨475203651159718898736535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633604868212958531648713 475203651159718898736535)
              ·
                refine ⟨712805476739578348104803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475203651159718898736535 712805476739578348104803)
                ·
                  refine ⟨1069208215109367522157205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712805476739578348104803 1069208215109367522157205)
                  ·
                    refine ⟨50119135083251602601119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1069208215109367522157205 50119135083251602601119)
                    ·
                      rfl

theorem cell22_146410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_146410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146410 prefixEnd_146410 := by exact prefixLift 146410
  have htrace : WordTrace (prefixWord ++ tailWord_146410) baseStart_146410 baseEnd_146410 := by
    simpa [prefixWord, tailWord_146410, baseEnd_146410] using wordTrace_append hprefix tailTrace_146410
  have hstable : (prefixWord ++ tailWord_146410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146410).length < 2 ^ (prefixWord ++ tailWord_146410).sum := by decide
  have hdescent : baseEnd_146410 < baseStart_146410 := by decide
  rcases family_descends (prefixWord ++ tailWord_146410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146446 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_146446 : Nat := 118140960795 + 146446 * 2 ^ 59
def prefixEnd_146446 : Nat := 4983230072969 + 3 ^ 40 * 146446 * 2
def baseEnd_146446 : Nat := 50131458618959508701009

theorem tailTrace_146446 : CollatzResearch.WordTrace tailWord_146446 prefixEnd_146446 50131458618959508701009 := by
  unfold tailWord_146446
  simp only [CollatzResearch.WordTrace]
  refine ⟨667665553432328478835399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3560882951639085220455461 667665553432328478835399)
  ·
    refine ⟨1001498330148492718253099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 667665553432328478835399 1001498330148492718253099)
    ·
      refine ⟨1502247495222739077379649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1001498330148492718253099 1502247495222739077379649)
      ·
        refine ⟨1126685621417054308034737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1502247495222739077379649 1126685621417054308034737)
        ·
          refine ⟨845014216062790731026053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126685621417054308034737 845014216062790731026053)
          ·
            refine ⟨158440165511773262067385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 845014216062790731026053 158440165511773262067385)
            ·
              refine ⟨118830124133829946550539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158440165511773262067385 118830124133829946550539)
              ·
                refine ⟨178245186200744919825809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118830124133829946550539 178245186200744919825809)
                ·
                  refine ⟨133683889650558689869357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178245186200744919825809 133683889650558689869357)
                  ·
                    refine ⟨50131458618959508701009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133683889650558689869357 50131458618959508701009)
                    ·
                      rfl

theorem cell22_146446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_146446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146446 prefixEnd_146446 := by exact prefixLift 146446
  have htrace : WordTrace (prefixWord ++ tailWord_146446) baseStart_146446 baseEnd_146446 := by
    simpa [prefixWord, tailWord_146446, baseEnd_146446] using wordTrace_append hprefix tailTrace_146446
  have hstable : (prefixWord ++ tailWord_146446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146446).length < 2 ^ (prefixWord ++ tailWord_146446).sum := by decide
  have hdescent : baseEnd_146446 < baseStart_146446 := by decide
  rcases family_descends (prefixWord ++ tailWord_146446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146450 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_146450 : Nat := 118140960795 + 146450 * 2 ^ 59
def prefixEnd_146450 : Nat := 4983230072969 + 3 ^ 40 * 146450 * 2
def baseEnd_146450 : Nat := 50132827900704831600997

theorem tailTrace_146450 : CollatzResearch.WordTrace tailWord_146450 prefixEnd_146450 50132827900704831600997 := by
  unfold tailWord_146450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335367579861034128457201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3560980212962757675885869 1335367579861034128457201)
  ·
    refine ⟨1001525684895775596342901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1335367579861034128457201 1001525684895775596342901)
    ·
      refine ⟨93893032958978962157147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1001525684895775596342901 93893032958978962157147)
      ·
        refine ⟨140839549438468443235721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93893032958978962157147 140839549438468443235721)
        ·
          refine ⟨105629662078851332426791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140839549438468443235721 105629662078851332426791)
          ·
            refine ⟨158444493118276998640187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105629662078851332426791 158444493118276998640187)
            ·
              refine ⟨237666739677415497960281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158444493118276998640187 237666739677415497960281)
              ·
                refine ⟨178250054758061623470211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237666739677415497960281 178250054758061623470211)
                ·
                  refine ⟨267375082137092435205317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178250054758061623470211 267375082137092435205317)
                  ·
                    refine ⟨50132827900704831600997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267375082137092435205317 50132827900704831600997)
                    ·
                      rfl

theorem cell22_146450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_146450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146450 prefixEnd_146450 := by exact prefixLift 146450
  have htrace : WordTrace (prefixWord ++ tailWord_146450) baseStart_146450 baseEnd_146450 := by
    simpa [prefixWord, tailWord_146450, baseEnd_146450] using wordTrace_append hprefix tailTrace_146450
  have hstable : (prefixWord ++ tailWord_146450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146450).length < 2 ^ (prefixWord ++ tailWord_146450).sum := by decide
  have hdescent : baseEnd_146450 < baseStart_146450 := by decide
  rcases family_descends (prefixWord ++ tailWord_146450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146485 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_146485 : Nat := 118140960795 + 146485 * 2 ^ 59
def prefixEnd_146485 : Nat := 4983230072969 + 3 ^ 40 * 146485 * 2
def baseEnd_146485 : Nat := 50144809115976406975889

theorem tailTrace_146485 : CollatzResearch.WordTrace tailWord_146485 prefixEnd_146485 50144809115976406975889 := by
  unfold tailWord_146485
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342746874317337491352909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3561831249544891660901939 5342746874317337491352909)
  ·
    refine ⟨2003530077869001559257341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5342746874317337491352909 2003530077869001559257341)
    ·
      refine ⟨751323779200875584721503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2003530077869001559257341 751323779200875584721503)
      ·
        refine ⟨1126985668801313377082255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751323779200875584721503 1126985668801313377082255)
        ·
          refine ⟨1690478503201970065623383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1126985668801313377082255 1690478503201970065623383)
          ·
            refine ⟨2535717754802955098435075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690478503201970065623383 2535717754802955098435075)
            ·
              refine ⟨3803576632204432647652613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535717754802955098435075 3803576632204432647652613)
              ·
                refine ⟨713170618538331121434865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3803576632204432647652613 713170618538331121434865)
                ·
                  refine ⟨534877963903748341076149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 713170618538331121434865 534877963903748341076149)
                  ·
                    refine ⟨50144809115976406975889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 534877963903748341076149 50144809115976406975889)
                    ·
                      rfl

theorem cell22_146485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_146485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146485 prefixEnd_146485 := by exact prefixLift 146485
  have htrace : WordTrace (prefixWord ++ tailWord_146485) baseStart_146485 baseEnd_146485 := by
    simpa [prefixWord, tailWord_146485, baseEnd_146485] using wordTrace_append hprefix tailTrace_146485
  have hstable : (prefixWord ++ tailWord_146485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146485).length < 2 ^ (prefixWord ++ tailWord_146485).sum := by decide
  have hdescent : baseEnd_146485 < baseStart_146485 := by decide
  rcases family_descends (prefixWord ++ tailWord_146485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146517 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_146517 : Nat := 118140960795 + 146517 * 2 ^ 59
def prefixEnd_146517 : Nat := 4983230072969 + 3 ^ 40 * 146517 * 2
def baseEnd_146517 : Nat := 50155763369938990175791

theorem tailTrace_146517 : CollatzResearch.WordTrace tailWord_146517 prefixEnd_146517 50155763369938990175791 := by
  unfold tailWord_146517
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343914010201406956517805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3562609340134271304345203 5343914010201406956517805)
  ·
    refine ⟨2003967753825527608694177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5343914010201406956517805 2003967753825527608694177)
    ·
      refine ⟨1502975815369145706520633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2003967753825527608694177 1502975815369145706520633)
      ·
        refine ⟨1127231861526859279890475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1502975815369145706520633 1127231861526859279890475)
        ·
          refine ⟨1690847792290288919835713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127231861526859279890475 1690847792290288919835713)
          ·
            refine ⟨1268135844217716689876785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1690847792290288919835713 1268135844217716689876785)
            ·
              refine ⟨951101883163287517407589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268135844217716689876785 951101883163287517407589)
              ·
                refine ⟨178331603093116409513923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 951101883163287517407589 178331603093116409513923)
                ·
                  refine ⟨267497404639674614270885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178331603093116409513923 267497404639674614270885)
                  ·
                    refine ⟨50155763369938990175791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267497404639674614270885 50155763369938990175791)
                    ·
                      rfl

theorem cell22_146517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_146517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146517 prefixEnd_146517 := by exact prefixLift 146517
  have htrace : WordTrace (prefixWord ++ tailWord_146517) baseStart_146517 baseEnd_146517 := by
    simpa [prefixWord, tailWord_146517, baseEnd_146517] using wordTrace_append hprefix tailTrace_146517
  have hstable : (prefixWord ++ tailWord_146517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146517).length < 2 ^ (prefixWord ++ tailWord_146517).sum := by decide
  have hdescent : baseEnd_146517 < baseStart_146517 := by decide
  rcases family_descends (prefixWord ++ tailWord_146517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146564 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_146564 : Nat := 118140960795 + 146564 * 2 ^ 59
def prefixEnd_146564 : Nat := 4983230072969 + 3 ^ 40 * 146564 * 2
def baseEnd_146564 : Nat := 50171852430446534250647

theorem tailTrace_146564 : CollatzResearch.WordTrace tailWord_146564 prefixEnd_146564 50171852430446534250647 := by
  unfold tailWord_146564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2672814120515566991739373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3563752160687422655652497 2672814120515566991739373)
  ·
    refine ⟨1002305295193337621902265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2672814120515566991739373 1002305295193337621902265)
    ·
      refine ⟨751728971395003216426699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1002305295193337621902265 751728971395003216426699)
      ·
        refine ⟨1127593457092504824640049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751728971395003216426699 1127593457092504824640049)
        ·
          refine ⟨845695092819378618480037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127593457092504824640049 845695092819378618480037)
          ·
            refine ⟨158567829903633490965007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 845695092819378618480037 158567829903633490965007)
            ·
              refine ⟨237851744855450236447511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158567829903633490965007 237851744855450236447511)
              ·
                refine ⟨356777617283175354671267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237851744855450236447511 356777617283175354671267)
                ·
                  refine ⟨535166425924763032006901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356777617283175354671267 535166425924763032006901)
                  ·
                    refine ⟨50171852430446534250647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 535166425924763032006901 50171852430446534250647)
                    ·
                      rfl

theorem cell22_146564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_146564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146564 prefixEnd_146564 := by exact prefixLift 146564
  have htrace : WordTrace (prefixWord ++ tailWord_146564) baseStart_146564 baseEnd_146564 := by
    simpa [prefixWord, tailWord_146564, baseEnd_146564] using wordTrace_append hprefix tailTrace_146564
  have hstable : (prefixWord ++ tailWord_146564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146564).length < 2 ^ (prefixWord ++ tailWord_146564).sum := by decide
  have hdescent : baseEnd_146564 < baseStart_146564 := by decide
  rcases family_descends (prefixWord ++ tailWord_146564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146594 : List Nat := [3, 3, 1, 3, 2, 2, 8]
def baseStart_146594 : Nat := 118140960795 + 146594 * 2 ^ 59
def prefixEnd_146594 : Nat := 4983230072969 + 3 ^ 40 * 146594 * 2
def baseEnd_146594 : Nat := 1858597112723572444465

theorem tailTrace_146594 : CollatzResearch.WordTrace tailWord_146594 prefixEnd_146594 1858597112723572444465 := by
  unfold tailWord_146594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336680607730612276767709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3564481620614966071380557 1336680607730612276767709)
  ·
    refine ⟨501255227898979603787891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1336680607730612276767709 501255227898979603787891)
    ·
      refine ⟨751882841848469405681837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501255227898979603787891 751882841848469405681837)
      ·
        refine ⟨281956065693176027130689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 751882841848469405681837 281956065693176027130689)
        ·
          refine ⟨211467049269882020348017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281956065693176027130689 211467049269882020348017)
          ·
            refine ⟨158600286952411515261013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211467049269882020348017 158600286952411515261013)
            ·
              refine ⟨1858597112723572444465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 158600286952411515261013 1858597112723572444465)
              ·
                rfl

theorem cell22_146594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 8].length) (baseStart_146594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146594 prefixEnd_146594 := by exact prefixLift 146594
  have htrace : WordTrace (prefixWord ++ tailWord_146594) baseStart_146594 baseEnd_146594 := by
    simpa [prefixWord, tailWord_146594, baseEnd_146594] using wordTrace_append hprefix tailTrace_146594
  have hstable : (prefixWord ++ tailWord_146594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146594).length < 2 ^ (prefixWord ++ tailWord_146594).sum := by decide
  have hdescent : baseEnd_146594 < baseStart_146594 := by decide
  rcases family_descends (prefixWord ++ tailWord_146594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146630 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_146630 : Nat := 118140960795 + 146630 * 2 ^ 59
def prefixEnd_146630 : Nat := 4983230072969 + 3 ^ 40 * 146630 * 2
def baseEnd_146630 : Nat := 50194445579244362100445

theorem tailTrace_146630 : CollatzResearch.WordTrace tailWord_146630 prefixEnd_146630 50194445579244362100445 := by
  unfold tailWord_146630
  simp only [CollatzResearch.WordTrace]
  refine ⟨167126108087250851730667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3565356972528018170254229 167126108087250851730667)
  ·
    refine ⟨250689162130876277596001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167126108087250851730667 250689162130876277596001)
    ·
      refine ⟨188016871598157208197001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250689162130876277596001 188016871598157208197001)
      ·
        refine ⟨141012653698617906147751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188016871598157208197001 141012653698617906147751)
        ·
          refine ⟨211518980547926859221627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141012653698617906147751 211518980547926859221627)
          ·
            refine ⟨317278470821890288832441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211518980547926859221627 317278470821890288832441)
            ·
              refine ⟨237958853116417716624331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317278470821890288832441 237958853116417716624331)
              ·
                refine ⟨356938279674626574936497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237958853116417716624331 356938279674626574936497)
                ·
                  refine ⟨267703709755969931202373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356938279674626574936497 267703709755969931202373)
                  ·
                    refine ⟨50194445579244362100445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267703709755969931202373 50194445579244362100445)
                    ·
                      rfl

theorem cell22_146630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_146630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146630 prefixEnd_146630 := by exact prefixLift 146630
  have htrace : WordTrace (prefixWord ++ tailWord_146630) baseStart_146630 baseEnd_146630 := by
    simpa [prefixWord, tailWord_146630, baseEnd_146630] using wordTrace_append hprefix tailTrace_146630
  have hstable : (prefixWord ++ tailWord_146630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146630).length < 2 ^ (prefixWord ++ tailWord_146630).sum := by decide
  have hdescent : baseEnd_146630 < baseStart_146630 := by decide
  rcases family_descends (prefixWord ++ tailWord_146630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146669 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_146669 : Nat := 118140960795 + 146669 * 2 ^ 59
def prefixEnd_146669 : Nat := 4983230072969 + 3 ^ 40 * 146669 * 2
def baseEnd_146669 : Nat := 50207796076261260375325

theorem tailTrace_146669 : CollatzResearch.WordTrace tailWord_146669 prefixEnd_146669 50207796076261260375325 := by
  unfold tailWord_146669
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349457905650736916051061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3566305270433824610700707 5349457905650736916051061)
  ·
    refine ⟨501511678654756585879787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5349457905650736916051061 501511678654756585879787)
    ·
      refine ⟨752267517982134878819681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501511678654756585879787 752267517982134878819681)
      ·
        refine ⟨564200638486601159114761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 752267517982134878819681 564200638486601159114761)
        ·
          refine ⟨423150478864950869336071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564200638486601159114761 423150478864950869336071)
          ·
            refine ⟨634725718297426304004107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423150478864950869336071 634725718297426304004107)
            ·
              refine ⟨952088577446139456006161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634725718297426304004107 952088577446139456006161)
              ·
                refine ⟨714066433084604592004621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952088577446139456006161 714066433084604592004621)
                ·
                  refine ⟨267774912406726722001733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714066433084604592004621 267774912406726722001733)
                  ·
                    refine ⟨50207796076261260375325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267774912406726722001733 50207796076261260375325)
                    ·
                      rfl

theorem cell22_146669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_146669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146669 prefixEnd_146669 := by exact prefixLift 146669
  have htrace : WordTrace (prefixWord ++ tailWord_146669) baseStart_146669 baseEnd_146669 := by
    simpa [prefixWord, tailWord_146669, baseEnd_146669] using wordTrace_append hprefix tailTrace_146669
  have hstable : (prefixWord ++ tailWord_146669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146669).length < 2 ^ (prefixWord ++ tailWord_146669).sum := by decide
  have hdescent : baseEnd_146669 < baseStart_146669 := by decide
  rcases family_descends (prefixWord ++ tailWord_146669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146684 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 6]
def baseStart_146684 : Nat := 118140960795 + 146684 * 2 ^ 59
def prefixEnd_146684 : Nat := 4983230072969 + 3 ^ 40 * 146684 * 2
def baseEnd_146684 : Nat := 16737643627602073750093

theorem tailTrace_146684 : CollatzResearch.WordTrace tailWord_146684 prefixEnd_146684 16737643627602073750093 := by
  unfold tailWord_146684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675002500298197238923553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3566670000397596318564737 2675002500298197238923553)
  ·
    refine ⟨2006251875223647929192665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2675002500298197238923553 2006251875223647929192665)
    ·
      refine ⟨1504688906417735946894499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2006251875223647929192665 1504688906417735946894499)
      ·
        refine ⟨2257033359626603920341749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504688906417735946894499 2257033359626603920341749)
        ·
          refine ⟨211596877464994117532039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2257033359626603920341749 211596877464994117532039)
          ·
            refine ⟨317395316197491176298059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211596877464994117532039 317395316197491176298059)
            ·
              refine ⟨476092974296236764447089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317395316197491176298059 476092974296236764447089)
              ·
                refine ⟨357069730722177573335317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476092974296236764447089 357069730722177573335317)
                ·
                  refine ⟨16737643627602073750093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 357069730722177573335317 16737643627602073750093)
                  ·
                    rfl

theorem cell22_146684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_146684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146684 prefixEnd_146684 := by exact prefixLift 146684
  have htrace : WordTrace (prefixWord ++ tailWord_146684) baseStart_146684 baseEnd_146684 := by
    simpa [prefixWord, tailWord_146684, baseEnd_146684] using wordTrace_append hprefix tailTrace_146684
  have hstable : (prefixWord ++ tailWord_146684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146684).length < 2 ^ (prefixWord ++ tailWord_146684).sum := by decide
  have hdescent : baseEnd_146684 < baseStart_146684 := by decide
  rcases family_descends (prefixWord ++ tailWord_146684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146697 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_146697 : Nat := 118140960795 + 146697 * 2 ^ 59
def prefixEnd_146697 : Nat := 4983230072969 + 3 ^ 40 * 146697 * 2
def baseEnd_146697 : Nat := 50217381048478520675239

theorem tailTrace_146697 : CollatzResearch.WordTrace tailWord_146697 prefixEnd_146697 50217381048478520675239 := by
  unfold tailWord_146697
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350479149549297698070345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3566986099699531798713563 5350479149549297698070345)
  ·
    refine ⟨4012859362161973273552759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5350479149549297698070345 4012859362161973273552759)
    ·
      refine ⟨6019289043242959910329139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012859362161973273552759 6019289043242959910329139)
      ·
        refine ⟨9028933564864439865493709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6019289043242959910329139 9028933564864439865493709)
        ·
          refine ⟨3385850086824164949560141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9028933564864439865493709 3385850086824164949560141)
          ·
            refine ⟨1269693782559061856085053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3385850086824164949560141 1269693782559061856085053)
            ·
              refine ⟨476135168459648196031895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1269693782559061856085053 476135168459648196031895)
              ·
                refine ⟨714202752689472294047843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476135168459648196031895 714202752689472294047843)
                ·
                  refine ⟨1071304129034208441071765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714202752689472294047843 1071304129034208441071765)
                  ·
                    refine ⟨50217381048478520675239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1071304129034208441071765 50217381048478520675239)
                    ·
                      rfl

theorem cell22_146697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_146697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146697 prefixEnd_146697 := by exact prefixLift 146697
  have htrace : WordTrace (prefixWord ++ tailWord_146697) baseStart_146697 baseEnd_146697 := by
    simpa [prefixWord, tailWord_146697, baseEnd_146697] using wordTrace_append hprefix tailTrace_146697
  have hstable : (prefixWord ++ tailWord_146697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146697).length < 2 ^ (prefixWord ++ tailWord_146697).sum := by decide
  have hdescent : baseEnd_146697 < baseStart_146697 := by decide
  rcases family_descends (prefixWord ++ tailWord_146697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146712 : List Nat := [2, 1, 2, 3, 1, 4, 9]
def baseStart_146712 : Nat := 118140960795 + 146712 * 2 ^ 59
def prefixEnd_146712 : Nat := 4983230072969 + 3 ^ 40 * 146712 * 2
def baseEnd_146712 : Nat := 1860093179815684501859

theorem tailTrace_146712 : CollatzResearch.WordTrace tailWord_146712 prefixEnd_146712 1860093179815684501859 := by
  unfold tailWord_146712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675513122247477629933195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3567350829663303506577593 2675513122247477629933195)
  ·
    refine ⟨4013269683371216444899793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2675513122247477629933195 4013269683371216444899793)
    ·
      refine ⟨3009952262528412333674845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4013269683371216444899793 3009952262528412333674845)
      ·
        refine ⟨1128732098448154625128067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3009952262528412333674845 1128732098448154625128067)
        ·
          refine ⟨1693098147672231937692101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128732098448154625128067 1693098147672231937692101)
          ·
            refine ⟨317455902688543488317269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1693098147672231937692101 317455902688543488317269)
            ·
              refine ⟨1860093179815684501859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 317455902688543488317269 1860093179815684501859)
              ·
                rfl

theorem cell22_146712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 9].length) (baseStart_146712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146712 prefixEnd_146712 := by exact prefixLift 146712
  have htrace : WordTrace (prefixWord ++ tailWord_146712) baseStart_146712 baseEnd_146712 := by
    simpa [prefixWord, tailWord_146712, baseEnd_146712] using wordTrace_append hprefix tailTrace_146712
  have hstable : (prefixWord ++ tailWord_146712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146712).length < 2 ^ (prefixWord ++ tailWord_146712).sum := by decide
  have hdescent : baseEnd_146712 < baseStart_146712 := by decide
  rcases family_descends (prefixWord ++ tailWord_146712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146716 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_146716 : Nat := 118140960795 + 146716 * 2 ^ 59
def prefixEnd_146716 : Nat := 4983230072969 + 3 ^ 40 * 146716 * 2
def baseEnd_146716 : Nat := 50223885136768804450181

theorem tailTrace_146716 : CollatzResearch.WordTrace tailWord_146716 prefixEnd_146716 50223885136768804450181 := by
  unfold tailWord_146716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675586068240231971506001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3567448090986975962008001 2675586068240231971506001)
  ·
    refine ⟨2006689551180173978629501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2675586068240231971506001 2006689551180173978629501)
    ·
      refine ⟨752508581692565241986063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2006689551180173978629501 752508581692565241986063)
      ·
        refine ⟨1128762872538847862979095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752508581692565241986063 1128762872538847862979095)
        ·
          refine ⟨1693144308808271794468643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128762872538847862979095 1693144308808271794468643)
          ·
            refine ⟨2539716463212407691702965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693144308808271794468643 2539716463212407691702965)
            ·
              refine ⟨238098418426163221097153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2539716463212407691702965 238098418426163221097153)
              ·
                refine ⟨178573813819622415822865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238098418426163221097153 178573813819622415822865)
                ·
                  refine ⟨133930360364716811867149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178573813819622415822865 133930360364716811867149)
                  ·
                    refine ⟨50223885136768804450181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133930360364716811867149 50223885136768804450181)
                    ·
                      rfl

theorem cell22_146716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_146716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146716 prefixEnd_146716 := by exact prefixLift 146716
  have htrace : WordTrace (prefixWord ++ tailWord_146716) baseStart_146716 baseEnd_146716 := by
    simpa [prefixWord, tailWord_146716, baseEnd_146716] using wordTrace_append hprefix tailTrace_146716
  have hstable : (prefixWord ++ tailWord_146716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146716).length < 2 ^ (prefixWord ++ tailWord_146716).sum := by decide
  have hdescent : baseEnd_146716 < baseStart_146716 := by decide
  rcases family_descends (prefixWord ++ tailWord_146716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146718 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_146718 : Nat := 118140960795 + 146718 * 2 ^ 59
def prefixEnd_146718 : Nat := 4983230072969 + 3 ^ 40 * 146718 * 2
def baseEnd_146718 : Nat := 16741523259213821966725

theorem tailTrace_146718 : CollatzResearch.WordTrace tailWord_146718 prefixEnd_146718 16741523259213821966725 := by
  unfold tailWord_146718
  simp only [CollatzResearch.WordTrace]
  refine ⟨668905635309152285573101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3567496721648812189723205 668905635309152285573101)
  ·
    refine ⟨250839613240932107089913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 668905635309152285573101 250839613240932107089913)
    ·
      refine ⟨188129709930699080317435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250839613240932107089913 188129709930699080317435)
      ·
        refine ⟨282194564896048620476153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188129709930699080317435 282194564896048620476153)
        ·
          refine ⟨211645923672036465357115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282194564896048620476153 211645923672036465357115)
          ·
            refine ⟨317468885508054698035673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211645923672036465357115 317468885508054698035673)
            ·
              refine ⟨238101664131041023526755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317468885508054698035673 238101664131041023526755)
              ·
                refine ⟨357152496196561535290133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238101664131041023526755 357152496196561535290133)
                ·
                  refine ⟨16741523259213821966725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 357152496196561535290133 16741523259213821966725)
                  ·
                    rfl

theorem cell22_146718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_146718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146718 prefixEnd_146718 := by exact prefixLift 146718
  have htrace : WordTrace (prefixWord ++ tailWord_146718) baseStart_146718 baseEnd_146718 := by
    simpa [prefixWord, tailWord_146718, baseEnd_146718] using wordTrace_append hprefix tailTrace_146718
  have hstable : (prefixWord ++ tailWord_146718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146718).length < 2 ^ (prefixWord ++ tailWord_146718).sum := by decide
  have hdescent : baseEnd_146718 < baseStart_146718 := by decide
  rcases family_descends (prefixWord ++ tailWord_146718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146733 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_146733 : Nat := 118140960795 + 146733 * 2 ^ 59
def prefixEnd_146733 : Nat := 4983230072969 + 3 ^ 40 * 146733 * 2
def baseEnd_146733 : Nat := 50229704584186426775129

theorem tailTrace_146733 : CollatzResearch.WordTrace tailWord_146733 prefixEnd_146733 50229704584186426775129 := by
  unfold tailWord_146733
  simp only [CollatzResearch.WordTrace]
  refine ⟨5351792177418875846380853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3567861451612583897587235 5351792177418875846380853)
  ·
    refine ⟨501730516633019610598205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5351792177418875846380853 501730516633019610598205)
    ·
      refine ⟨188148943737382353974327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 501730516633019610598205 188148943737382353974327)
      ·
        refine ⟨282223415606073530961491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188148943737382353974327 282223415606073530961491)
        ·
          refine ⟨423335123409110296442237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282223415606073530961491 423335123409110296442237)
          ·
            refine ⟨158750671278416361165839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423335123409110296442237 158750671278416361165839)
            ·
              refine ⟨238126006917624541748759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158750671278416361165839 238126006917624541748759)
              ·
                refine ⟨357189010376436812623139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238126006917624541748759 357189010376436812623139)
                ·
                  refine ⟨535783515564655218934709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357189010376436812623139 535783515564655218934709)
                  ·
                    refine ⟨50229704584186426775129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 535783515564655218934709 50229704584186426775129)
                    ·
                      rfl

theorem cell22_146733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_146733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146733 prefixEnd_146733 := by exact prefixLift 146733
  have htrace : WordTrace (prefixWord ++ tailWord_146733) baseStart_146733 baseEnd_146733 := by
    simpa [prefixWord, tailWord_146733, baseEnd_146733] using wordTrace_append hprefix tailTrace_146733
  have hstable : (prefixWord ++ tailWord_146733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146733).length < 2 ^ (prefixWord ++ tailWord_146733).sum := by decide
  have hdescent : baseEnd_146733 < baseStart_146733 := by decide
  rcases family_descends (prefixWord ++ tailWord_146733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146791 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 5]
def baseStart_146791 : Nat := 118140960795 + 146791 * 2 ^ 59
def prefixEnd_146791 : Nat := 4983230072969 + 3 ^ 40 * 146791 * 2
def baseEnd_146791 : Nat := 16749853056497869608317

theorem tailTrace_146791 : CollatzResearch.WordTrace tailWord_146791 prefixEnd_146791 16749853056497869608317 := by
  unfold tailWord_146791
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353907611208751751992227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3569271740805834501328151 5353907611208751751992227)
  ·
    refine ⟨8030861416813127627988341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353907611208751751992227 8030861416813127627988341)
    ·
      refine ⟨752893257826230715123907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8030861416813127627988341 752893257826230715123907)
      ·
        refine ⟨1129339886739346072685861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752893257826230715123907 1129339886739346072685861)
        ·
          refine ⟨211751228763627388628599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1129339886739346072685861 211751228763627388628599)
          ·
            refine ⟨317626843145441082942899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211751228763627388628599 317626843145441082942899)
            ·
              refine ⟨476440264718161624414349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317626843145441082942899 476440264718161624414349)
              ·
                refine ⟨178665099269310609155381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 476440264718161624414349 178665099269310609155381)
                ·
                  refine ⟨16749853056497869608317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178665099269310609155381 16749853056497869608317)
                  ·
                    rfl

theorem cell22_146791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 5].length) (baseStart_146791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146791 prefixEnd_146791 := by exact prefixLift 146791
  have htrace : WordTrace (prefixWord ++ tailWord_146791) baseStart_146791 baseEnd_146791 := by
    simpa [prefixWord, tailWord_146791, baseEnd_146791] using wordTrace_append hprefix tailTrace_146791
  have hstable : (prefixWord ++ tailWord_146791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146791).length < 2 ^ (prefixWord ++ tailWord_146791).sum := by decide
  have hdescent : baseEnd_146791 < baseStart_146791 := by decide
  rcases family_descends (prefixWord ++ tailWord_146791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146851 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 2, 3]
def baseStart_146851 : Nat := 118140960795 + 146851 * 2 ^ 59
def prefixEnd_146851 : Nat := 4983230072969 + 3 ^ 40 * 146851 * 2
def baseEnd_146851 : Nat := 50270098395673452324767

theorem tailTrace_146851 : CollatzResearch.WordTrace tailWord_146851 prefixEnd_146851 50270098395673452324767 := by
  unfold tailWord_146851
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356095990991381999176407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3570730660660921332784271 5356095990991381999176407)
  ·
    refine ⟨8034143986487072998764611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5356095990991381999176407 8034143986487072998764611)
    ·
      refine ⟨12051215979730609498146917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8034143986487072998764611 12051215979730609498146917)
      ·
        refine ⟨2259602996199489280902547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12051215979730609498146917 2259602996199489280902547)
        ·
          refine ⟨3389404494299233921353821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259602996199489280902547 3389404494299233921353821)
          ·
            refine ⟨1271026685362212720507683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3389404494299233921353821 1271026685362212720507683)
            ·
              refine ⟨1906540028043319080761525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271026685362212720507683 1906540028043319080761525)
              ·
                refine ⟨178738127629061163821393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1906540028043319080761525 178738127629061163821393)
                ·
                  refine ⟨134053595721795872866045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178738127629061163821393 134053595721795872866045)
                  ·
                    refine ⟨50270098395673452324767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134053595721795872866045 50270098395673452324767)
                    ·
                      rfl

theorem cell22_146851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 3].length) (baseStart_146851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146851 prefixEnd_146851 := by exact prefixLift 146851
  have htrace : WordTrace (prefixWord ++ tailWord_146851) baseStart_146851 baseEnd_146851 := by
    simpa [prefixWord, tailWord_146851, baseEnd_146851] using wordTrace_append hprefix tailTrace_146851
  have hstable : (prefixWord ++ tailWord_146851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146851).length < 2 ^ (prefixWord ++ tailWord_146851).sum := by decide
  have hdescent : baseEnd_146851 < baseStart_146851 := by decide
  rcases family_descends (prefixWord ++ tailWord_146851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146894 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_146894 : Nat := 118140960795 + 146894 * 2 ^ 59
def prefixEnd_146894 : Nat := 4983230072969 + 3 ^ 40 * 146894 * 2
def baseEnd_146894 : Nat := 50284818174435673499635

theorem tailTrace_146894 : CollatzResearch.WordTrace tailWord_146894 prefixEnd_146894 50284818174435673499635 := by
  unfold tailWord_146894
  simp only [CollatzResearch.WordTrace]
  refine ⟨669708041229450042873967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3571776219890400228661157 669708041229450042873967)
  ·
    refine ⟨1004562061844175064310951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 669708041229450042873967 1004562061844175064310951)
    ·
      refine ⟨1506843092766262596466427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004562061844175064310951 1506843092766262596466427)
      ·
        refine ⟨2260264639149393894699641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506843092766262596466427 2260264639149393894699641)
        ·
          refine ⟨1695198479362045421024731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260264639149393894699641 1695198479362045421024731)
          ·
            refine ⟨2542797719043068131537097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695198479362045421024731 2542797719043068131537097)
            ·
              refine ⟨1907098289282301098652823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542797719043068131537097 1907098289282301098652823)
              ·
                refine ⟨2860647433923451647979235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907098289282301098652823 2860647433923451647979235)
                ·
                  refine ⟨4290971150885177471968853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2860647433923451647979235 4290971150885177471968853)
                  ·
                    refine ⟨50284818174435673499635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4290971150885177471968853 50284818174435673499635)
                    ·
                      rfl

theorem cell22_146894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_146894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146894 prefixEnd_146894 := by exact prefixLift 146894
  have htrace : WordTrace (prefixWord ++ tailWord_146894) baseStart_146894 baseEnd_146894 := by
    simpa [prefixWord, tailWord_146894, baseEnd_146894] using wordTrace_append hprefix tailTrace_146894
  have hstable : (prefixWord ++ tailWord_146894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146894).length < 2 ^ (prefixWord ++ tailWord_146894).sum := by decide
  have hdescent : baseEnd_146894 < baseStart_146894 := by decide
  rcases family_descends (prefixWord ++ tailWord_146894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146902 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_146902 : Nat := 118140960795 + 146902 * 2 ^ 59
def prefixEnd_146902 : Nat := 4983230072969 + 3 ^ 40 * 146902 * 2
def baseEnd_146902 : Nat := 50287556737926319299611

theorem tailTrace_146902 : CollatzResearch.WordTrace tailWord_146902 prefixEnd_146902 50287556737926319299611 := by
  unfold tailWord_146902
  simp only [CollatzResearch.WordTrace]
  refine ⟨334872257112913606830185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3571970742537745139521973 334872257112913606830185)
  ·
    refine ⟨251154192834685205122639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 334872257112913606830185 251154192834685205122639)
    ·
      refine ⟨376731289252027807683959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251154192834685205122639 376731289252027807683959)
      ·
        refine ⟨565096933878041711525939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376731289252027807683959 565096933878041711525939)
        ·
          refine ⟨847645400817062567288909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565096933878041711525939 847645400817062567288909)
          ·
            refine ⟨317867025306398462733341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 847645400817062567288909 317867025306398462733341)
            ·
              refine ⟨119200134489899423525003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317867025306398462733341 119200134489899423525003)
              ·
                refine ⟨178800201734849135287505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119200134489899423525003 178800201734849135287505)
                ·
                  refine ⟨134100151301136851465629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178800201734849135287505 134100151301136851465629)
                  ·
                    refine ⟨50287556737926319299611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134100151301136851465629 50287556737926319299611)
                    ·
                      rfl

theorem cell22_146902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_146902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146902 prefixEnd_146902 := by exact prefixLift 146902
  have htrace : WordTrace (prefixWord ++ tailWord_146902) baseStart_146902 baseEnd_146902 := by
    simpa [prefixWord, tailWord_146902, baseEnd_146902] using wordTrace_append hprefix tailTrace_146902
  have hstable : (prefixWord ++ tailWord_146902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146902).length < 2 ^ (prefixWord ++ tailWord_146902).sum := by decide
  have hdescent : baseEnd_146902 < baseStart_146902 := by decide
  rcases family_descends (prefixWord ++ tailWord_146902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146924 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_146924 : Nat := 118140960795 + 146924 * 2 ^ 59
def prefixEnd_146924 : Nat := 4983230072969 + 3 ^ 40 * 146924 * 2
def baseEnd_146924 : Nat := 50295087787525595249543

theorem tailTrace_146924 : CollatzResearch.WordTrace tailWord_146924 prefixEnd_146924 50295087787525595249543 := by
  unfold tailWord_146924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679379259863457733291913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3572505679817943644389217 2679379259863457733291913)
  ·
    refine ⟨2009534444897593299968935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2679379259863457733291913 2009534444897593299968935)
    ·
      refine ⟨3014301667346389949953403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2009534444897593299968935 3014301667346389949953403)
      ·
        refine ⟨4521452501019584924930105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014301667346389949953403 4521452501019584924930105)
        ·
          refine ⟨3391089375764688693697579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4521452501019584924930105 3391089375764688693697579)
          ·
            refine ⟨5086634063647033040546369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391089375764688693697579 5086634063647033040546369)
            ·
              refine ⟨3814975547735274780409777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5086634063647033040546369 3814975547735274780409777)
              ·
                refine ⟨2861231660801456085307333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3814975547735274780409777 2861231660801456085307333)
                ·
                  refine ⟨536480936400273015995125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2861231660801456085307333 536480936400273015995125)
                  ·
                    refine ⟨50295087787525595249543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 536480936400273015995125 50295087787525595249543)
                    ·
                      rfl

theorem cell22_146924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_146924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146924 prefixEnd_146924 := by exact prefixLift 146924
  have htrace : WordTrace (prefixWord ++ tailWord_146924) baseStart_146924 baseEnd_146924 := by
    simpa [prefixWord, tailWord_146924, baseEnd_146924] using wordTrace_append hprefix tailTrace_146924
  have hstable : (prefixWord ++ tailWord_146924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146924).length < 2 ^ (prefixWord ++ tailWord_146924).sum := by decide
  have hdescent : baseEnd_146924 < baseStart_146924 := by decide
  rcases family_descends (prefixWord ++ tailWord_146924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146999 : List Nat := [1, 1, 3, 1, 2, 14]
def baseStart_146999 : Nat := 118140960795 + 146999 * 2 ^ 59
def prefixEnd_146999 : Nat := 4983230072969 + 3 ^ 40 * 146999 * 2
def baseEnd_146999 : Nat := 621243973089511106473

theorem tailTrace_146999 : CollatzResearch.WordTrace tailWord_146999 prefixEnd_146999 621243973089511106473 := by
  unfold tailWord_146999
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361493994455203275564051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3574329329636802183709367 5361493994455203275564051)
  ·
    refine ⟨8042240991682804913346077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5361493994455203275564051 8042240991682804913346077)
    ·
      refine ⟨3015840371881051842504779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8042240991682804913346077 3015840371881051842504779)
      ·
        refine ⟨4523760557821577763757169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015840371881051842504779 4523760557821577763757169)
        ·
          refine ⟨3392820418366183322817877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4523760557821577763757169 3392820418366183322817877)
          ·
            refine ⟨621243973089511106473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 3392820418366183322817877 621243973089511106473)
            ·
              rfl

theorem cell22_146999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 14].length) (baseStart_146999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_146999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_146999 prefixEnd_146999 := by exact prefixLift 146999
  have htrace : WordTrace (prefixWord ++ tailWord_146999) baseStart_146999 baseEnd_146999 := by
    simpa [prefixWord, tailWord_146999, baseEnd_146999] using wordTrace_append hprefix tailTrace_146999
  have hstable : (prefixWord ++ tailWord_146999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146999).length < 2 ^ (prefixWord ++ tailWord_146999).sum := by decide
  have hdescent : baseEnd_146999 < baseStart_146999 := by decide
  rcases family_descends (prefixWord ++ tailWord_146999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147005 : List Nat := [1, 4, 1, 3, 3, 1, 1, 4, 4]
def baseStart_147005 : Nat := 118140960795 + 147005 * 2 ^ 59
def prefixEnd_147005 : Nat := 4983230072969 + 3 ^ 40 * 147005 * 2
def baseEnd_147005 : Nat := 16774271914289461324765

theorem tailTrace_147005 : CollatzResearch.WordTrace tailWord_147005 prefixEnd_147005 16774271914289461324765 := by
  unfold tailWord_147005
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361712832433466300282469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3574475221622310866854979 5361712832433466300282469)
  ·
    refine ⟨1005321156081274931302963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5361712832433466300282469 1005321156081274931302963)
    ·
      refine ⟨1507981734121912396954445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005321156081274931302963 1507981734121912396954445)
      ·
        refine ⟨565493150295717148857917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1507981734121912396954445 565493150295717148857917)
        ·
          refine ⟨212059931360893930821719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 565493150295717148857917 212059931360893930821719)
          ·
            refine ⟨318089897041340896232579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212059931360893930821719 318089897041340896232579)
            ·
              refine ⟨477134845562011344348869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318089897041340896232579 477134845562011344348869)
              ·
                refine ⟨89462783542877127065413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477134845562011344348869 89462783542877127065413)
                ·
                  refine ⟨16774271914289461324765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89462783542877127065413 16774271914289461324765)
                  ·
                    rfl

theorem cell22_147005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_147005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147005 prefixEnd_147005 := by exact prefixLift 147005
  have htrace : WordTrace (prefixWord ++ tailWord_147005) baseStart_147005 baseEnd_147005 := by
    simpa [prefixWord, tailWord_147005, baseEnd_147005] using wordTrace_append hprefix tailTrace_147005
  have hstable : (prefixWord ++ tailWord_147005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147005).length < 2 ^ (prefixWord ++ tailWord_147005).sum := by decide
  have hdescent : baseEnd_147005 < baseStart_147005 := by decide
  rcases family_descends (prefixWord ++ tailWord_147005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147054 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_147054 : Nat := 118140960795 + 147054 * 2 ^ 59
def prefixEnd_147054 : Nat := 4983230072969 + 3 ^ 40 * 147054 * 2
def baseEnd_147054 : Nat := 50339589444248589499145

theorem tailTrace_147054 : CollatzResearch.WordTrace tailWord_147054 prefixEnd_147054 50339589444248589499145 := by
  unfold tailWord_147054
  simp only [CollatzResearch.WordTrace]
  refine ⟨670437501156993458602027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3575666672837298445877477 670437501156993458602027)
  ·
    refine ⟨1005656251735490187903041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670437501156993458602027 1005656251735490187903041)
    ·
      refine ⟨754242188801617640927281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1005656251735490187903041 754242188801617640927281)
      ·
        refine ⟨565681641601213230695461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 754242188801617640927281 565681641601213230695461)
        ·
          refine ⟨106065307800227480755399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 565681641601213230695461 106065307800227480755399)
          ·
            refine ⟨159097961700341221133099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106065307800227480755399 159097961700341221133099)
            ·
              refine ⟨238646942550511831699649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159097961700341221133099 238646942550511831699649)
              ·
                refine ⟨178985206912883873774737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238646942550511831699649 178985206912883873774737)
                ·
                  refine ⟨134238905184662905331053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178985206912883873774737 134238905184662905331053)
                  ·
                    refine ⟨50339589444248589499145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134238905184662905331053 50339589444248589499145)
                    ·
                      rfl

theorem cell22_147054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_147054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147054 prefixEnd_147054 := by exact prefixLift 147054
  have htrace : WordTrace (prefixWord ++ tailWord_147054) baseStart_147054 baseEnd_147054 := by
    simpa [prefixWord, tailWord_147054, baseEnd_147054] using wordTrace_append hprefix tailTrace_147054
  have hstable : (prefixWord ++ tailWord_147054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147054).length < 2 ^ (prefixWord ++ tailWord_147054).sum := by decide
  have hdescent : baseEnd_147054 < baseStart_147054 := by decide
  rcases family_descends (prefixWord ++ tailWord_147054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147065 : List Nat := [1, 2, 1, 3, 3, 1, 1, 6, 1, 3]
def baseStart_147065 : Nat := 118140960795 + 147065 * 2 ^ 59
def prefixEnd_147065 : Nat := 4983230072969 + 3 ^ 40 * 147065 * 2
def baseEnd_147065 : Nat := 50343354969048227474111

theorem tailTrace_147065 : CollatzResearch.WordTrace tailWord_147065 prefixEnd_147065 50343354969048227474111 := by
  unfold tailWord_147065
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363901212216096547466649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3575934141477397698311099 5363901212216096547466649)
  ·
    refine ⟨4022925909162072410599987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5363901212216096547466649 4022925909162072410599987)
    ·
      refine ⟨6034388863743108615899981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4022925909162072410599987 6034388863743108615899981)
      ·
        refine ⟨2262895823903665730962493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6034388863743108615899981 2262895823903665730962493)
        ·
          refine ⟨848585933963874649110935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2262895823903665730962493 848585933963874649110935)
          ·
            refine ⟨1272878900945811973666403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848585933963874649110935 1272878900945811973666403)
            ·
              refine ⟨1909318351418717960499605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272878900945811973666403 1909318351418717960499605)
              ·
                refine ⟨89499297722752404398419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1909318351418717960499605 89499297722752404398419)
                ·
                  refine ⟨134248946584128606597629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89499297722752404398419 134248946584128606597629)
                  ·
                    refine ⟨50343354969048227474111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134248946584128606597629 50343354969048227474111)
                    ·
                      rfl

theorem cell22_147065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 3].length) (baseStart_147065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147065 prefixEnd_147065 := by exact prefixLift 147065
  have htrace : WordTrace (prefixWord ++ tailWord_147065) baseStart_147065 baseEnd_147065 := by
    simpa [prefixWord, tailWord_147065, baseEnd_147065] using wordTrace_append hprefix tailTrace_147065
  have hstable : (prefixWord ++ tailWord_147065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147065).length < 2 ^ (prefixWord ++ tailWord_147065).sum := by decide
  have hdescent : baseEnd_147065 < baseStart_147065 := by decide
  rcases family_descends (prefixWord ++ tailWord_147065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147153 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_147153 : Nat := 118140960795 + 147153 * 2 ^ 59
def prefixEnd_147153 : Nat := 4983230072969 + 3 ^ 40 * 147153 * 2
def baseEnd_147153 : Nat := 50373479167445331273841

theorem tailTrace_147153 : CollatzResearch.WordTrace tailWord_147153 prefixEnd_147153 50373479167445331273841 := by
  unfold tailWord_147153
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367110835897287576670113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3578073890598191717780075 5367110835897287576670113)
  ·
    refine ⟨4025333126922965682502585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5367110835897287576670113 4025333126922965682502585)
    ·
      refine ⟨3018999845192224261876939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4025333126922965682502585 3018999845192224261876939)
      ·
        refine ⟨4528499767788336392815409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3018999845192224261876939 4528499767788336392815409)
        ·
          refine ⟨3396374825841252294611557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4528499767788336392815409 3396374825841252294611557)
          ·
            refine ⟨636820279845234805239667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3396374825841252294611557 636820279845234805239667)
            ·
              refine ⟨955230419767852207859501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636820279845234805239667 955230419767852207859501)
              ·
                refine ⟨358211407412944577947313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955230419767852207859501 358211407412944577947313)
                ·
                  refine ⟨268658555559708433460485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358211407412944577947313 268658555559708433460485)
                  ·
                    refine ⟨50373479167445331273841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 268658555559708433460485 50373479167445331273841)
                    ·
                      rfl

theorem cell22_147153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_147153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147153 prefixEnd_147153 := by exact prefixLift 147153
  have htrace : WordTrace (prefixWord ++ tailWord_147153) baseStart_147153 baseEnd_147153 := by
    simpa [prefixWord, tailWord_147153, baseEnd_147153] using wordTrace_append hprefix tailTrace_147153
  have hstable : (prefixWord ++ tailWord_147153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147153).length < 2 ^ (prefixWord ++ tailWord_147153).sum := by decide
  have hdescent : baseEnd_147153 < baseStart_147153 := by decide
  rcases family_descends (prefixWord ++ tailWord_147153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147228 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_147228 : Nat := 118140960795 + 147228 * 2 ^ 59
def prefixEnd_147228 : Nat := 4983230072969 + 3 ^ 40 * 147228 * 2
def baseEnd_147228 : Nat := 50399153200170135648611

theorem tailTrace_147228 : CollatzResearch.WordTrace tailWord_147228 prefixEnd_147228 50399153200170135648611 := by
  unfold tailWord_147228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684923155312787692825169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3579897540417050257100225 2684923155312787692825169)
  ·
    refine ⟨2013692366484590769618877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2684923155312787692825169 2013692366484590769618877)
    ·
      refine ⟨755134637431721538607079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2013692366484590769618877 755134637431721538607079)
      ·
        refine ⟨1132701956147582307910619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755134637431721538607079 1132701956147582307910619)
        ·
          refine ⟨1699052934221373461865929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132701956147582307910619 1699052934221373461865929)
          ·
            refine ⟨1274289700666030096399447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1699052934221373461865929 1274289700666030096399447)
            ·
              refine ⟨1911434550999045144599171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274289700666030096399447 1911434550999045144599171)
              ·
                refine ⟨2867151826498567716898757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911434550999045144599171 2867151826498567716898757)
                ·
                  refine ⟨537590967468481446918517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2867151826498567716898757 537590967468481446918517)
                  ·
                    refine ⟨50399153200170135648611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 537590967468481446918517 50399153200170135648611)
                    ·
                      rfl

theorem cell22_147228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_147228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147228 prefixEnd_147228 := by exact prefixLift 147228
  have htrace : WordTrace (prefixWord ++ tailWord_147228) baseStart_147228 baseEnd_147228 := by
    simpa [prefixWord, tailWord_147228, baseEnd_147228] using wordTrace_append hprefix tailTrace_147228
  have hstable : (prefixWord ++ tailWord_147228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147228).length < 2 ^ (prefixWord ++ tailWord_147228).sum := by decide
  have hdescent : baseEnd_147228 < baseStart_147228 := by decide
  rcases family_descends (prefixWord ++ tailWord_147228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147260 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_147260 : Nat := 118140960795 + 147260 * 2 ^ 59
def prefixEnd_147260 : Nat := 4983230072969 + 3 ^ 40 * 147260 * 2
def baseEnd_147260 : Nat := 50410107454132718848513

theorem tailTrace_147260 : CollatzResearch.WordTrace tailWord_147260 prefixEnd_147260 50410107454132718848513 := by
  unfold tailWord_147260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2685506723254822425407617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3580675631006429900543489 2685506723254822425407617)
  ·
    refine ⟨2014130042441116819055713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2685506723254822425407617 2014130042441116819055713)
    ·
      refine ⟨1510597531830837614291785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2014130042441116819055713 1510597531830837614291785)
      ·
        refine ⟨1132948148873128210718839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1510597531830837614291785 1132948148873128210718839)
        ·
          refine ⟨1699422223309692316078259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132948148873128210718839 1699422223309692316078259)
          ·
            refine ⟨2549133334964538474117389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699422223309692316078259 2549133334964538474117389)
            ·
              refine ⟨955925000611701927794021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2549133334964538474117389 955925000611701927794021)
              ·
                refine ⟨179235937614694111461379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 955925000611701927794021 179235937614694111461379)
                ·
                  refine ⟨268853906422041167192069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179235937614694111461379 268853906422041167192069)
                  ·
                    refine ⟨50410107454132718848513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 268853906422041167192069 50410107454132718848513)
                    ·
                      rfl

theorem cell22_147260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_147260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147260 prefixEnd_147260 := by exact prefixLift 147260
  have htrace : WordTrace (prefixWord ++ tailWord_147260) baseStart_147260 baseEnd_147260 := by
    simpa [prefixWord, tailWord_147260, baseEnd_147260] using wordTrace_append hprefix tailTrace_147260
  have hstable : (prefixWord ++ tailWord_147260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147260).length < 2 ^ (prefixWord ++ tailWord_147260).sum := by decide
  have hdescent : baseEnd_147260 < baseStart_147260 := by decide
  rcases family_descends (prefixWord ++ tailWord_147260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147273 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_147273 : Nat := 118140960795 + 147273 * 2 ^ 59
def prefixEnd_147273 : Nat := 4983230072969 + 3 ^ 40 * 147273 * 2
def baseEnd_147273 : Nat := 50414557619805018273473

theorem tailTrace_147273 : CollatzResearch.WordTrace tailWord_147273 prefixEnd_147273 50414557619805018273473 := by
  unfold tailWord_147273
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371487595462548071038473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3580991730308365380692315 5371487595462548071038473)
  ·
    refine ⟨4028615696596911053278855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5371487595462548071038473 4028615696596911053278855)
    ·
      refine ⟨6042923544895366579918283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4028615696596911053278855 6042923544895366579918283)
      ·
        refine ⟨9064385317343049869877425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042923544895366579918283 9064385317343049869877425)
        ·
          refine ⟨6798288988007287402408069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9064385317343049869877425 6798288988007287402408069)
          ·
            refine ⟨1274679185251366387951513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6798288988007287402408069 1274679185251366387951513)
            ·
              refine ⟨956009388938524790963635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274679185251366387951513 956009388938524790963635)
              ·
                refine ⟨1434014083407787186445453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956009388938524790963635 1434014083407787186445453)
                ·
                  refine ⟨537755281277920194917045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1434014083407787186445453 537755281277920194917045)
                  ·
                    refine ⟨50414557619805018273473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 537755281277920194917045 50414557619805018273473)
                    ·
                      rfl

theorem cell22_147273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_147273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147273 prefixEnd_147273 := by exact prefixLift 147273
  have htrace : WordTrace (prefixWord ++ tailWord_147273) baseStart_147273 baseEnd_147273 := by
    simpa [prefixWord, tailWord_147273, baseEnd_147273] using wordTrace_append hprefix tailTrace_147273
  have hstable : (prefixWord ++ tailWord_147273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147273).length < 2 ^ (prefixWord ++ tailWord_147273).sum := by decide
  have hdescent : baseEnd_147273 < baseStart_147273 := by decide
  rcases family_descends (prefixWord ++ tailWord_147273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147290 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_147290 : Nat := 118140960795 + 147290 * 2 ^ 59
def prefixEnd_147290 : Nat := 4983230072969 + 3 ^ 40 * 147290 * 2
def baseEnd_147290 : Nat := 50420377067222640598421

theorem tailTrace_147290 : CollatzResearch.WordTrace tailWord_147290 prefixEnd_147290 50420377067222640598421 := by
  unfold tailWord_147290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343026909100239993601831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3581405090933973316271549 1343026909100239993601831)
  ·
    refine ⟨2014540363650359990402747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343026909100239993601831 2014540363650359990402747)
    ·
      refine ⟨3021810545475539985604121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014540363650359990402747 3021810545475539985604121)
      ·
        refine ⟨2266357909106654989203091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3021810545475539985604121 2266357909106654989203091)
        ·
          refine ⟨3399536863659982483804637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266357909106654989203091 3399536863659982483804637)
          ·
            refine ⟨1274826323872493431426739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3399536863659982483804637 1274826323872493431426739)
            ·
              refine ⟨1912239485808740147140109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274826323872493431426739 1912239485808740147140109)
              ·
                refine ⟨717089807178277555177541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1912239485808740147140109 717089807178277555177541)
                ·
                  refine ⟨134454338845927041595789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717089807178277555177541 134454338845927041595789)
                  ·
                    refine ⟨50420377067222640598421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134454338845927041595789 50420377067222640598421)
                    ·
                      rfl

theorem cell22_147290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_147290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147290 prefixEnd_147290 := by exact prefixLift 147290
  have htrace : WordTrace (prefixWord ++ tailWord_147290) baseStart_147290 baseEnd_147290 := by
    simpa [prefixWord, tailWord_147290, baseEnd_147290] using wordTrace_append hprefix tailTrace_147290
  have hstable : (prefixWord ++ tailWord_147290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147290).length < 2 ^ (prefixWord ++ tailWord_147290).sum := by decide
  have hdescent : baseEnd_147290 < baseStart_147290 := by decide
  rcases family_descends (prefixWord ++ tailWord_147290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147440 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_147440 : Nat := 118140960795 + 147440 * 2 ^ 59
def prefixEnd_147440 : Nat := 4983230072969 + 3 ^ 40 * 147440 * 2
def baseEnd_147440 : Nat := 50471725132672249347961

theorem tailTrace_147440 : CollatzResearch.WordTrace tailWord_147440 prefixEnd_147440 50471725132672249347961 := by
  unfold tailWord_147440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688789292928767796183887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3585052390571690394911849 2688789292928767796183887)
  ·
    refine ⟨4033183939393151694275831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2688789292928767796183887 4033183939393151694275831)
    ·
      refine ⟨6049775909089727541413747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033183939393151694275831 6049775909089727541413747)
      ·
        refine ⟨9074663863634591312120621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049775909089727541413747 9074663863634591312120621)
        ·
          refine ⟨3402998948862971742045233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9074663863634591312120621 3402998948862971742045233)
          ·
            refine ⟨2552249211647228806533925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3402998948862971742045233 2552249211647228806533925)
            ·
              refine ⟨478546727183855401225111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2552249211647228806533925 478546727183855401225111)
              ·
                refine ⟨717820090775783101837667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478546727183855401225111 717820090775783101837667)
                ·
                  refine ⟨1076730136163674652756501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717820090775783101837667 1076730136163674652756501)
                  ·
                    refine ⟨50471725132672249347961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1076730136163674652756501 50471725132672249347961)
                    ·
                      rfl

theorem cell22_147440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_147440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147440 prefixEnd_147440 := by exact prefixLift 147440
  have htrace : WordTrace (prefixWord ++ tailWord_147440) baseStart_147440 baseEnd_147440 := by
    simpa [prefixWord, tailWord_147440, baseEnd_147440] using wordTrace_append hprefix tailTrace_147440
  have hstable : (prefixWord ++ tailWord_147440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147440).length < 2 ^ (prefixWord ++ tailWord_147440).sum := by decide
  have hdescent : baseEnd_147440 < baseStart_147440 := by decide
  rcases family_descends (prefixWord ++ tailWord_147440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147457 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_147457 : Nat := 118140960795 + 147457 * 2 ^ 59
def prefixEnd_147457 : Nat := 4983230072969 + 3 ^ 40 * 147457 * 2
def baseEnd_147457 : Nat := 50477544580089871672909

theorem tailTrace_147457 : CollatzResearch.WordTrace tailWord_147457 prefixEnd_147457 50477544580089871672909 := by
  unfold tailWord_147457
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378198626795947495736625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3585465751197298330491083 5378198626795947495736625)
  ·
    refine ⟨4033648970096960621802469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5378198626795947495736625 4033648970096960621802469)
    ·
      refine ⟨756309181893180116587963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4033648970096960621802469 756309181893180116587963)
      ·
        refine ⟨1134463772839770174881945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756309181893180116587963 1134463772839770174881945)
        ·
          refine ⟨850847829629827631161459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1134463772839770174881945 850847829629827631161459)
          ·
            refine ⟨1276271744444741446742189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850847829629827631161459 1276271744444741446742189)
            ·
              refine ⟨478601904166778042528321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1276271744444741446742189 478601904166778042528321)
              ·
                refine ⟨358951428125083531896241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 478601904166778042528321 358951428125083531896241)
                ·
                  refine ⟨269213571093812648922181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358951428125083531896241 269213571093812648922181)
                  ·
                    refine ⟨50477544580089871672909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269213571093812648922181 50477544580089871672909)
                    ·
                      rfl

theorem cell22_147457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_147457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147457 prefixEnd_147457 := by exact prefixLift 147457
  have htrace : WordTrace (prefixWord ++ tailWord_147457) baseStart_147457 baseEnd_147457 := by
    simpa [prefixWord, tailWord_147457, baseEnd_147457] using wordTrace_append hprefix tailTrace_147457
  have hstable : (prefixWord ++ tailWord_147457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147457).length < 2 ^ (prefixWord ++ tailWord_147457).sum := by decide
  have hdescent : baseEnd_147457 < baseStart_147457 := by decide
  rcases family_descends (prefixWord ++ tailWord_147457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147487 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 5, 3]
def baseStart_147487 : Nat := 118140960795 + 147487 * 2 ^ 59
def prefixEnd_147487 : Nat := 4983230072969 + 3 ^ 40 * 147487 * 2
def baseEnd_147487 : Nat := 50487814193179793422817

theorem tailTrace_147487 : CollatzResearch.WordTrace tailWord_147487 prefixEnd_147487 50487814193179793422817 := by
  unfold tailWord_147487
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379292816687262619328715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3586195211124841746219143 5379292816687262619328715)
  ·
    refine ⟨8068939225030893928993073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5379292816687262619328715 8068939225030893928993073)
    ·
      refine ⟨6051704418773170446744805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8068939225030893928993073 6051704418773170446744805)
      ·
        refine ⟨1134694578519969458764651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6051704418773170446744805 1134694578519969458764651)
        ·
          refine ⟨1702041867779954188146977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134694578519969458764651 1702041867779954188146977)
          ·
            refine ⟨1276531400834965641110233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702041867779954188146977 1276531400834965641110233)
            ·
              refine ⟨957398550626224230832675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276531400834965641110233 957398550626224230832675)
              ·
                refine ⟨1436097825939336346249013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957398550626224230832675 1436097825939336346249013)
                ·
                  refine ⟨134634171181812782460845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436097825939336346249013 134634171181812782460845)
                  ·
                    refine ⟨50487814193179793422817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134634171181812782460845 50487814193179793422817)
                    ·
                      rfl

theorem cell22_147487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_147487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147487 prefixEnd_147487 := by exact prefixLift 147487
  have htrace : WordTrace (prefixWord ++ tailWord_147487) baseStart_147487 baseEnd_147487 := by
    simpa [prefixWord, tailWord_147487, baseEnd_147487] using wordTrace_append hprefix tailTrace_147487
  have hstable : (prefixWord ++ tailWord_147487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147487).length < 2 ^ (prefixWord ++ tailWord_147487).sum := by decide
  have hdescent : baseEnd_147487 < baseStart_147487 := by decide
  rcases family_descends (prefixWord ++ tailWord_147487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147500 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 7]
def baseStart_147500 : Nat := 118140960795 + 147500 * 2 ^ 59
def prefixEnd_147500 : Nat := 4983230072969 + 3 ^ 40 * 147500 * 2
def baseEnd_147500 : Nat := 16830754786284030949259

theorem tailTrace_147500 : CollatzResearch.WordTrace tailWord_147500 prefixEnd_147500 16830754786284030949259 := by
  unfold tailWord_147500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689883482820082919775977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3586511310426777226367969 2689883482820082919775977)
  ·
    refine ⟨2017412612115062189831983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2689883482820082919775977 2017412612115062189831983)
    ·
      refine ⟨3026118918172593284747975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2017412612115062189831983 3026118918172593284747975)
      ·
        refine ⟨4539178377258889927121963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026118918172593284747975 4539178377258889927121963)
        ·
          refine ⟨6808767565888334890682945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539178377258889927121963 6808767565888334890682945)
          ·
            refine ⟨5106575674416251168012209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6808767565888334890682945 5106575674416251168012209)
            ·
              refine ⟨3829931755812188376009157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5106575674416251168012209 3829931755812188376009157)
              ·
                refine ⟨718112204214785320501717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3829931755812188376009157 718112204214785320501717)
                ·
                  refine ⟨16830754786284030949259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 718112204214785320501717 16830754786284030949259)
                  ·
                    rfl

theorem cell22_147500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_147500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147500 prefixEnd_147500 := by exact prefixLift 147500
  have htrace : WordTrace (prefixWord ++ tailWord_147500) baseStart_147500 baseEnd_147500 := by
    simpa [prefixWord, tailWord_147500, baseEnd_147500] using wordTrace_append hprefix tailTrace_147500
  have hstable : (prefixWord ++ tailWord_147500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147500).length < 2 ^ (prefixWord ++ tailWord_147500).sum := by decide
  have hdescent : baseEnd_147500 < baseStart_147500 := by decide
  rcases family_descends (prefixWord ++ tailWord_147500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147515 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 4, 5]
def baseStart_147515 : Nat := 118140960795 + 147515 * 2 ^ 59
def prefixEnd_147515 : Nat := 4983230072969 + 3 ^ 40 * 147515 * 2
def baseEnd_147515 : Nat := 50497399165397053722731

theorem tailTrace_147515 : CollatzResearch.WordTrace tailWord_147515 prefixEnd_147515 50497399165397053722731 := by
  unfold tailWord_147515
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380314060585823401347999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3586876040390548934231999 5380314060585823401347999)
  ·
    refine ⟨8070471090878735102021999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5380314060585823401347999 8070471090878735102021999)
    ·
      refine ⟨12105706636318102653032999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8070471090878735102021999 12105706636318102653032999)
      ·
        refine ⟨18158559954477153979549499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12105706636318102653032999 18158559954477153979549499)
        ·
          refine ⟨27237839931715730969324249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18158559954477153979549499 27237839931715730969324249)
          ·
            refine ⟨20428379948786798226993187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27237839931715730969324249 20428379948786798226993187)
            ·
              refine ⟨30642569923180197340489781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20428379948786798226993187 30642569923180197340489781)
              ·
                refine ⟨2872740930298143500670917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30642569923180197340489781 2872740930298143500670917)
                ·
                  refine ⟨538638924430901906375797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2872740930298143500670917 538638924430901906375797)
                  ·
                    refine ⟨50497399165397053722731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 538638924430901906375797 50497399165397053722731)
                    ·
                      rfl

theorem cell22_147515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_147515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147515 prefixEnd_147515 := by exact prefixLift 147515
  have htrace : WordTrace (prefixWord ++ tailWord_147515) baseStart_147515 baseEnd_147515 := by
    simpa [prefixWord, tailWord_147515, baseEnd_147515] using wordTrace_append hprefix tailTrace_147515
  have hstable : (prefixWord ++ tailWord_147515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147515).length < 2 ^ (prefixWord ++ tailWord_147515).sum := by decide
  have hdescent : baseEnd_147515 < baseStart_147515 := by decide
  rcases family_descends (prefixWord ++ tailWord_147515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147564 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_147564 : Nat := 118140960795 + 147564 * 2 ^ 59
def prefixEnd_147564 : Nat := 4983230072969 + 3 ^ 40 * 147564 * 2
def baseEnd_147564 : Nat := 50514172866777259247581

theorem tailTrace_147564 : CollatzResearch.WordTrace tailWord_147564 prefixEnd_147564 50514172866777259247581 := by
  unfold tailWord_147564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691050618704152384940873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3588067491605536513254497 2691050618704152384940873)
  ·
    refine ⟨2018287964028114288705655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2691050618704152384940873 2018287964028114288705655)
    ·
      refine ⟨3027431946042171433058483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018287964028114288705655 3027431946042171433058483)
      ·
        refine ⟨4541147919063257149587725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027431946042171433058483 4541147919063257149587725)
        ·
          refine ⟨1702930469648721431095397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4541147919063257149587725 1702930469648721431095397)
          ·
            refine ⟨319299463059135268330387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1702930469648721431095397 319299463059135268330387)
            ·
              refine ⟨478949194588702902495581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319299463059135268330387 478949194588702902495581)
              ·
                refine ⟨179605947970763588435843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 478949194588702902495581 179605947970763588435843)
                ·
                  refine ⟨269408921956145382653765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179605947970763588435843 269408921956145382653765)
                  ·
                    refine ⟨50514172866777259247581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269408921956145382653765 50514172866777259247581)
                    ·
                      rfl

theorem cell22_147564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_147564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147564 prefixEnd_147564 := by exact prefixLift 147564
  have htrace : WordTrace (prefixWord ++ tailWord_147564) baseStart_147564 baseEnd_147564 := by
    simpa [prefixWord, tailWord_147564, baseEnd_147564] using wordTrace_append hprefix tailTrace_147564
  have hstable : (prefixWord ++ tailWord_147564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147564).length < 2 ^ (prefixWord ++ tailWord_147564).sum := by decide
  have hdescent : baseEnd_147564 < baseStart_147564 := by decide
  rcases family_descends (prefixWord ++ tailWord_147564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147594 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_147594 : Nat := 118140960795 + 147594 * 2 ^ 59
def prefixEnd_147594 : Nat := 4983230072969 + 3 ^ 40 * 147594 * 2
def baseEnd_147594 : Nat := 50524442479867180997489

theorem tailTrace_147594 : CollatzResearch.WordTrace tailWord_147594 prefixEnd_147594 50524442479867180997489 := by
  unfold tailWord_147594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345798856824904973368459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3588796951533079928982557 1345798856824904973368459)
  ·
    refine ⟨2018698285237357460052689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345798856824904973368459 2018698285237357460052689)
    ·
      refine ⟨1514023713928018095039517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2018698285237357460052689 1514023713928018095039517)
      ·
        refine ⟨567758892723006785639819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1514023713928018095039517 567758892723006785639819)
        ·
          refine ⟨851638339084510178459729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567758892723006785639819 851638339084510178459729)
          ·
            refine ⟨638728754313382633844797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 851638339084510178459729 638728754313382633844797)
            ·
              refine ⟨239523282867518487691799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 638728754313382633844797 239523282867518487691799)
              ·
                refine ⟨359284924301277731537699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239523282867518487691799 359284924301277731537699)
                ·
                  refine ⟨538927386451916597306549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359284924301277731537699 538927386451916597306549)
                  ·
                    refine ⟨50524442479867180997489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 538927386451916597306549 50524442479867180997489)
                    ·
                      rfl

theorem cell22_147594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_147594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147594 prefixEnd_147594 := by exact prefixLift 147594
  have htrace : WordTrace (prefixWord ++ tailWord_147594) baseStart_147594 baseEnd_147594 := by
    simpa [prefixWord, tailWord_147594, baseEnd_147594] using wordTrace_append hprefix tailTrace_147594
  have hstable : (prefixWord ++ tailWord_147594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147594).length < 2 ^ (prefixWord ++ tailWord_147594).sum := by decide
  have hdescent : baseEnd_147594 < baseStart_147594 := by decide
  rcases family_descends (prefixWord ++ tailWord_147594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147606 : List Nat := [5, 3, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_147606 : Nat := 118140960795 + 147606 * 2 ^ 59
def prefixEnd_147606 : Nat := 4983230072969 + 3 ^ 40 * 147606 * 2
def baseEnd_147606 : Nat := 50528550325103149697453

theorem tailTrace_147606 : CollatzResearch.WordTrace tailWord_147606 prefixEnd_147606 50528550325103149697453 := by
  unfold tailWord_147606
  simp only [CollatzResearch.WordTrace]
  refine ⟨336477068953509121431917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3589088735504097295273781 336477068953509121431917)
  ·
    refine ⟨126178900857565920536969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 336477068953509121431917 126178900857565920536969)
    ·
      refine ⟨94634175643174440402727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126178900857565920536969 94634175643174440402727)
      ·
        refine ⟨141951263464761660604091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94634175643174440402727 141951263464761660604091)
        ·
          refine ⟨212926895197142490906137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141951263464761660604091 212926895197142490906137)
          ·
            refine ⟨159695171397856868179603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212926895197142490906137 159695171397856868179603)
            ·
              refine ⟨239542757096785302269405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159695171397856868179603 239542757096785302269405)
              ·
                refine ⟨89828533911294488351027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239542757096785302269405 89828533911294488351027)
                ·
                  refine ⟨134742800866941732526541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89828533911294488351027 134742800866941732526541)
                  ·
                    refine ⟨50528550325103149697453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134742800866941732526541 50528550325103149697453)
                    ·
                      rfl

theorem cell22_147606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_147606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147606 prefixEnd_147606 := by exact prefixLift 147606
  have htrace : WordTrace (prefixWord ++ tailWord_147606) baseStart_147606 baseEnd_147606 := by
    simpa [prefixWord, tailWord_147606, baseEnd_147606] using wordTrace_append hprefix tailTrace_147606
  have hstable : (prefixWord ++ tailWord_147606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147606).length < 2 ^ (prefixWord ++ tailWord_147606).sum := by decide
  have hdescent : baseEnd_147606 < baseStart_147606 := by decide
  rcases family_descends (prefixWord ++ tailWord_147606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147630 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_147630 : Nat := 118140960795 + 147630 * 2 ^ 59
def prefixEnd_147630 : Nat := 4983230072969 + 3 ^ 40 * 147630 * 2
def baseEnd_147630 : Nat := 16845588671858362365793

theorem tailTrace_147630 : CollatzResearch.WordTrace tailWord_147630 prefixEnd_147630 16845588671858362365793 := by
  unfold tailWord_147630
  simp only [CollatzResearch.WordTrace]
  refine ⟨673063556896149755223043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3589672303446132027856229 673063556896149755223043)
  ·
    refine ⟨1009595335344224632834565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673063556896149755223043 1009595335344224632834565)
    ·
      refine ⟨189299125377042118656481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1009595335344224632834565 189299125377042118656481)
      ·
        refine ⟨141974344032781588992361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189299125377042118656481 141974344032781588992361)
        ·
          refine ⟨106480758024586191744271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141974344032781588992361 106480758024586191744271)
          ·
            refine ⟨159721137036879287616407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106480758024586191744271 159721137036879287616407)
            ·
              refine ⟨239581705555318931424611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159721137036879287616407 239581705555318931424611)
              ·
                refine ⟨359372558332978397136917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239581705555318931424611 359372558332978397136917)
                ·
                  refine ⟨16845588671858362365793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 359372558332978397136917 16845588671858362365793)
                  ·
                    rfl

theorem cell22_147630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_147630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147630 prefixEnd_147630 := by exact prefixLift 147630
  have htrace : WordTrace (prefixWord ++ tailWord_147630) baseStart_147630 baseEnd_147630 := by
    simpa [prefixWord, tailWord_147630, baseEnd_147630] using wordTrace_append hprefix tailTrace_147630
  have hstable : (prefixWord ++ tailWord_147630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147630).length < 2 ^ (prefixWord ++ tailWord_147630).sum := by decide
  have hdescent : baseEnd_147630 < baseStart_147630 := by decide
  rcases family_descends (prefixWord ++ tailWord_147630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147729 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_147729 : Nat := 118140960795 + 147729 * 2 ^ 59
def prefixEnd_147729 : Nat := 4983230072969 + 3 ^ 40 * 147729 * 2
def baseEnd_147729 : Nat := 50570655738771828872075

theorem tailTrace_147729 : CollatzResearch.WordTrace tailWord_147729 prefixEnd_147729 50570655738771828872075 := by
  unfold tailWord_147729
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388119281810537949638241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3592079521207025299758827 5388119281810537949638241)
  ·
    refine ⟨4041089461357903462228681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5388119281810537949638241 4041089461357903462228681)
    ·
      refine ⟨3030817096018427596671511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4041089461357903462228681 3030817096018427596671511)
      ·
        refine ⟨4546225644027641395007267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030817096018427596671511 4546225644027641395007267)
        ·
          refine ⟨6819338466041462092510901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4546225644027641395007267 6819338466041462092510901)
          ·
            refine ⟨639312981191387071172897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6819338466041462092510901 639312981191387071172897)
            ·
              refine ⟨479484735893540303379673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639312981191387071172897 479484735893540303379673)
              ·
                refine ⟨359613551920155227534755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479484735893540303379673 359613551920155227534755)
                ·
                  refine ⟨539420327880232841302133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359613551920155227534755 539420327880232841302133)
                  ·
                    refine ⟨50570655738771828872075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 539420327880232841302133 50570655738771828872075)
                    ·
                      rfl

theorem cell22_147729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_147729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147729 prefixEnd_147729 := by exact prefixLift 147729
  have htrace : WordTrace (prefixWord ++ tailWord_147729) baseStart_147729 baseEnd_147729 := by
    simpa [prefixWord, tailWord_147729, baseEnd_147729] using wordTrace_append hprefix tailTrace_147729
  have hstable : (prefixWord ++ tailWord_147729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147729).length < 2 ^ (prefixWord ++ tailWord_147729).sum := by decide
  have hdescent : baseEnd_147729 < baseStart_147729 := by decide
  rcases family_descends (prefixWord ++ tailWord_147729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147763 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 2, 3]
def baseStart_147763 : Nat := 118140960795 + 147763 * 2 ^ 59
def prefixEnd_147763 : Nat := 4983230072969 + 3 ^ 40 * 147763 * 2
def baseEnd_147763 : Nat := 50582294633607073521971

theorem tailTrace_147763 : CollatzResearch.WordTrace tailWord_147763 prefixEnd_147763 50582294633607073521971 := by
  unfold tailWord_147763
  simp only [CollatzResearch.WordTrace]
  refine ⟨5389359363687361756375943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3592906242458241170917295 5389359363687361756375943)
  ·
    refine ⟨8084039045531042634563915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5389359363687361756375943 8084039045531042634563915)
    ·
      refine ⟨12126058568296563951845873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8084039045531042634563915 12126058568296563951845873)
      ·
        refine ⟨9094543926222422963884405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12126058568296563951845873 9094543926222422963884405)
        ·
          refine ⟨852613493083352152864163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9094543926222422963884405 852613493083352152864163)
          ·
            refine ⟨1278920239625028229296245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852613493083352152864163 1278920239625028229296245)
            ·
              refine ⟨119898772464846396496523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1278920239625028229296245 119898772464846396496523)
              ·
                refine ⟨179848158697269594744785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119898772464846396496523 179848158697269594744785)
                ·
                  refine ⟨134886119022952196058589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179848158697269594744785 134886119022952196058589)
                  ·
                    refine ⟨50582294633607073521971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134886119022952196058589 50582294633607073521971)
                    ·
                      rfl

theorem cell22_147763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 3].length) (baseStart_147763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147763 prefixEnd_147763 := by exact prefixLift 147763
  have htrace : WordTrace (prefixWord ++ tailWord_147763) baseStart_147763 baseEnd_147763 := by
    simpa [prefixWord, tailWord_147763, baseEnd_147763] using wordTrace_append hprefix tailTrace_147763
  have hstable : (prefixWord ++ tailWord_147763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147763).length < 2 ^ (prefixWord ++ tailWord_147763).sum := by decide
  have hdescent : baseEnd_147763 < baseStart_147763 := by decide
  rcases family_descends (prefixWord ++ tailWord_147763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147821 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 5]
def baseStart_147821 : Nat := 118140960795 + 147821 * 2 ^ 59
def prefixEnd_147821 : Nat := 4983230072969 + 3 ^ 40 * 147821 * 2
def baseEnd_147821 : Nat := 16867383072971418523931

theorem tailTrace_147821 : CollatzResearch.WordTrace tailWord_147821 prefixEnd_147821 16867383072971418523931 := by
  unfold tailWord_147821
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391474797477237661987317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3594316531651491774658211 5391474797477237661987317)
  ·
    refine ⟨505450762263491030811311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5391474797477237661987317 505450762263491030811311)
    ·
      refine ⟨758176143395236546216967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505450762263491030811311 758176143395236546216967)
      ·
        refine ⟨1137264215092854819325451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758176143395236546216967 1137264215092854819325451)
        ·
          refine ⟨1705896322639282228988177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137264215092854819325451 1705896322639282228988177)
          ·
            refine ⟨1279422241979461671741133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1705896322639282228988177 1279422241979461671741133)
            ·
              refine ⟨479783340742298126902925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1279422241979461671741133 479783340742298126902925)
              ·
                refine ⟨179918752778361797588597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 479783340742298126902925 179918752778361797588597)
                ·
                  refine ⟨16867383072971418523931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179918752778361797588597 16867383072971418523931)
                  ·
                    rfl

theorem cell22_147821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_147821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147821 prefixEnd_147821 := by exact prefixLift 147821
  have htrace : WordTrace (prefixWord ++ tailWord_147821) baseStart_147821 baseEnd_147821 := by
    simpa [prefixWord, tailWord_147821, baseEnd_147821] using wordTrace_append hprefix tailTrace_147821
  have hstable : (prefixWord ++ tailWord_147821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147821).length < 2 ^ (prefixWord ++ tailWord_147821).sum := by decide
  have hdescent : baseEnd_147821 < baseStart_147821 := by decide
  rcases family_descends (prefixWord ++ tailWord_147821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147900 : List Nat := [2, 2, 2, 4, 1, 2, 2, 3, 4]
def baseStart_147900 : Nat := 118140960795 + 147900 * 2 ^ 59
def prefixEnd_147900 : Nat := 4983230072969 + 3 ^ 40 * 147900 * 2
def baseEnd_147900 : Nat := 16876397511128127615517

theorem tailTrace_147900 : CollatzResearch.WordTrace tailWord_147900 prefixEnd_147900 16876397511128127615517 := by
  unfold tailWord_147900
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697178082095517077056577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3596237442794022769408769 2697178082095517077056577)
  ·
    refine ⟨2022883561571637807792433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2697178082095517077056577 2022883561571637807792433)
    ·
      refine ⟨1517162671178728355844325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2022883561571637807792433 1517162671178728355844325)
      ·
        refine ⟨284468000846011566720811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1517162671178728355844325 284468000846011566720811)
        ·
          refine ⟨426702001269017350081217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284468000846011566720811 426702001269017350081217)
          ·
            refine ⟨320026500951763012560913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426702001269017350081217 320026500951763012560913)
            ·
              refine ⟨240019875713822259420685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320026500951763012560913 240019875713822259420685)
              ·
                refine ⟨90007453392683347282757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240019875713822259420685 90007453392683347282757)
                ·
                  refine ⟨16876397511128127615517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90007453392683347282757 16876397511128127615517)
                  ·
                    rfl

theorem cell22_147900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_147900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147900 prefixEnd_147900 := by exact prefixLift 147900
  have htrace : WordTrace (prefixWord ++ tailWord_147900) baseStart_147900 baseEnd_147900 := by
    simpa [prefixWord, tailWord_147900, baseEnd_147900] using wordTrace_append hprefix tailTrace_147900
  have hstable : (prefixWord ++ tailWord_147900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147900).length < 2 ^ (prefixWord ++ tailWord_147900).sum := by decide
  have hdescent : baseEnd_147900 < baseStart_147900 := by decide
  rcases family_descends (prefixWord ++ tailWord_147900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147909 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_147909 : Nat := 118140960795 + 147909 * 2 ^ 59
def prefixEnd_147909 : Nat := 4983230072969 + 3 ^ 40 * 147909 * 2
def baseEnd_147909 : Nat := 50632273417311359371523

theorem tailTrace_147909 : CollatzResearch.WordTrace tailWord_147909 prefixEnd_147909 50632273417311359371523 := by
  unfold tailWord_147909
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394684421158428691190781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3596456280772285794127187 5394684421158428691190781)
  ·
    refine ⟨2023006657934410759196543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5394684421158428691190781 2023006657934410759196543)
    ·
      refine ⟨3034509986901616138794815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023006657934410759196543 3034509986901616138794815)
      ·
        refine ⟨4551764980352424208192223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3034509986901616138794815 4551764980352424208192223)
        ·
          refine ⟨6827647470528636312288335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551764980352424208192223 6827647470528636312288335)
          ·
            refine ⟨10241471205792954468432503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6827647470528636312288335 10241471205792954468432503)
            ·
              refine ⟨15362206808689431702648755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10241471205792954468432503 15362206808689431702648755)
              ·
                refine ⟨23043310213034147553973133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15362206808689431702648755 23043310213034147553973133)
                ·
                  refine ⟨8641241329887805332739925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23043310213034147553973133 8641241329887805332739925)
                  ·
                    refine ⟨50632273417311359371523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 8641241329887805332739925 50632273417311359371523)
                    ·
                      rfl

theorem cell22_147909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_147909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147909 prefixEnd_147909 := by exact prefixLift 147909
  have htrace : WordTrace (prefixWord ++ tailWord_147909) baseStart_147909 baseEnd_147909 := by
    simpa [prefixWord, tailWord_147909, baseEnd_147909] using wordTrace_append hprefix tailTrace_147909
  have hstable : (prefixWord ++ tailWord_147909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147909).length < 2 ^ (prefixWord ++ tailWord_147909).sum := by decide
  have hdescent : baseEnd_147909 < baseStart_147909 := by decide
  rcases family_descends (prefixWord ++ tailWord_147909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147943 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 3, 3]
def baseStart_147943 : Nat := 118140960795 + 147943 * 2 ^ 59
def prefixEnd_147943 : Nat := 4983230072969 + 3 ^ 40 * 147943 * 2
def baseEnd_147943 : Nat := 50643912312146604021419

theorem tailTrace_147943 : CollatzResearch.WordTrace tailWord_147943 prefixEnd_147943 50643912312146604021419 := by
  unfold tailWord_147943
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395924503035252497928483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3597283002023501665285655 5395924503035252497928483)
  ·
    refine ⟨8093886754552878746892725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5395924503035252497928483 8093886754552878746892725)
    ·
      refine ⟨758801883239332382521193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8093886754552878746892725 758801883239332382521193)
      ·
        refine ⟨569101412429499286890895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 758801883239332382521193 569101412429499286890895)
        ·
          refine ⟨853652118644248930336343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569101412429499286890895 853652118644248930336343)
          ·
            refine ⟨1280478177966373395504515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853652118644248930336343 1280478177966373395504515)
            ·
              refine ⟨1920717266949560093256773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280478177966373395504515 1920717266949560093256773)
              ·
                refine ⟨360134487553042517485645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1920717266949560093256773 360134487553042517485645)
                ·
                  refine ⟨135050432832390944057117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360134487553042517485645 135050432832390944057117)
                  ·
                    refine ⟨50643912312146604021419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135050432832390944057117 50643912312146604021419)
                    ·
                      rfl

theorem cell22_147943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_147943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_147943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_147943 prefixEnd_147943 := by exact prefixLift 147943
  have htrace : WordTrace (prefixWord ++ tailWord_147943) baseStart_147943 baseEnd_147943 := by
    simpa [prefixWord, tailWord_147943, baseEnd_147943] using wordTrace_append hprefix tailTrace_147943
  have hstable : (prefixWord ++ tailWord_147943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147943).length < 2 ^ (prefixWord ++ tailWord_147943).sum := by decide
  have hdescent : baseEnd_147943 < baseStart_147943 := by decide
  rcases family_descends (prefixWord ++ tailWord_147943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148001 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 8]
def baseStart_148001 : Nat := 118140960795 + 148001 * 2 ^ 59
def prefixEnd_148001 : Nat := 4983230072969 + 3 ^ 40 * 148001 * 2
def baseEnd_148001 : Nat := 16887922299151262023747

theorem tailTrace_148001 : CollatzResearch.WordTrace tailWord_148001 prefixEnd_148001 16887922299151262023747 := by
  unfold tailWord_148001
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398039936825128403539857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3598693291216752269026571 5398039936825128403539857)
  ·
    refine ⟨4048529952618846302654893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5398039936825128403539857 4048529952618846302654893)
    ·
      refine ⟨1518198732232067363495585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4048529952618846302654893 1518198732232067363495585)
      ·
        refine ⟨1138649049174050522621689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1518198732232067363495585 1138649049174050522621689)
        ·
          refine ⟨853986786880537891966267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138649049174050522621689 853986786880537891966267)
          ·
            refine ⟨1280980180320806837949401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853986786880537891966267 1280980180320806837949401)
            ·
              refine ⟨960735135240605128462051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280980180320806837949401 960735135240605128462051)
              ·
                refine ⟨1441102702860907692693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960735135240605128462051 1441102702860907692693077)
                ·
                  refine ⟨16887922299151262023747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1441102702860907692693077 16887922299151262023747)
                  ·
                    rfl

theorem cell22_148001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_148001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148001 prefixEnd_148001 := by exact prefixLift 148001
  have htrace : WordTrace (prefixWord ++ tailWord_148001) baseStart_148001 baseEnd_148001 := by
    simpa [prefixWord, tailWord_148001, baseEnd_148001] using wordTrace_append hprefix tailTrace_148001
  have hstable : (prefixWord ++ tailWord_148001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148001).length < 2 ^ (prefixWord ++ tailWord_148001).sum := by decide
  have hdescent : baseEnd_148001 < baseStart_148001 := by decide
  rcases family_descends (prefixWord ++ tailWord_148001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148003 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 3, 4]
def baseStart_148003 : Nat := 118140960795 + 148003 * 2 ^ 59
def prefixEnd_148003 : Nat := 4983230072969 + 3 ^ 40 * 148003 * 2
def baseEnd_148003 : Nat := 50664451538326447521235

theorem tailTrace_148003 : CollatzResearch.WordTrace tailWord_148003 prefixEnd_148003 50664451538326447521235 := by
  unfold tailWord_148003
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398112882817882745112663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3598741921878588496741775 5398112882817882745112663)
  ·
    refine ⟨8097169324226824117668995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5398112882817882745112663 8097169324226824117668995)
    ·
      refine ⟨12145753986340236176503493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8097169324226824117668995 12145753986340236176503493)
      ·
        refine ⟨2277328872438794283094405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12145753986340236176503493 2277328872438794283094405)
        ·
          refine ⟨426999163582273928080201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2277328872438794283094405 426999163582273928080201)
          ·
            refine ⟨320249372686705446060151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426999163582273928080201 320249372686705446060151)
            ·
              refine ⟨480374059030058169090227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320249372686705446060151 480374059030058169090227)
              ·
                refine ⟨720561088545087253635341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480374059030058169090227 720561088545087253635341)
                ·
                  refine ⟨270210408204407720113253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720561088545087253635341 270210408204407720113253)
                  ·
                    refine ⟨50664451538326447521235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270210408204407720113253 50664451538326447521235)
                    ·
                      rfl

theorem cell22_148003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_148003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148003 prefixEnd_148003 := by exact prefixLift 148003
  have htrace : WordTrace (prefixWord ++ tailWord_148003) baseStart_148003 baseEnd_148003 := by
    simpa [prefixWord, tailWord_148003, baseEnd_148003] using wordTrace_append hprefix tailTrace_148003
  have hstable : (prefixWord ++ tailWord_148003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148003).length < 2 ^ (prefixWord ++ tailWord_148003).sum := by decide
  have hdescent : baseEnd_148003 < baseStart_148003 := by decide
  rcases family_descends (prefixWord ++ tailWord_148003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148016 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_148016 : Nat := 118140960795 + 148016 * 2 ^ 59
def prefixEnd_148016 : Nat := 4983230072969 + 3 ^ 40 * 148016 * 2
def baseEnd_148016 : Nat := 50668901703998746946195

theorem tailTrace_148016 : CollatzResearch.WordTrace tailWord_148016 prefixEnd_148016 50668901703998746946195 := by
  unfold tailWord_148016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699293515885392982667951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3599058021180523976890601 2699293515885392982667951)
  ·
    refine ⟨4048940273828089474001927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699293515885392982667951 4048940273828089474001927)
    ·
      refine ⟨6073410410742134211002891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048940273828089474001927 6073410410742134211002891)
      ·
        refine ⟨9110115616113201316504337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073410410742134211002891 9110115616113201316504337)
        ·
          refine ⟨6832586712084900987378253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9110115616113201316504337 6832586712084900987378253)
          ·
            refine ⟨2562220017031837870266845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6832586712084900987378253 2562220017031837870266845)
            ·
              refine ⟨960832506386939201350067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2562220017031837870266845 960832506386939201350067)
              ·
                refine ⟨1441248759580408802025101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960832506386939201350067 1441248759580408802025101)
                ·
                  refine ⟨540468284842653300759413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1441248759580408802025101 540468284842653300759413)
                  ·
                    refine ⟨50668901703998746946195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 540468284842653300759413 50668901703998746946195)
                    ·
                      rfl

theorem cell22_148016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_148016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148016 prefixEnd_148016 := by exact prefixLift 148016
  have htrace : WordTrace (prefixWord ++ tailWord_148016) baseStart_148016 baseEnd_148016 := by
    simpa [prefixWord, tailWord_148016, baseEnd_148016] using wordTrace_append hprefix tailTrace_148016
  have hstable : (prefixWord ++ tailWord_148016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148016).length < 2 ^ (prefixWord ++ tailWord_148016).sum := by decide
  have hdescent : baseEnd_148016 < baseStart_148016 := by decide
  rcases family_descends (prefixWord ++ tailWord_148016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148050 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_148050 : Nat := 118140960795 + 148050 * 2 ^ 59
def prefixEnd_148050 : Nat := 4983230072969 + 3 ^ 40 * 148050 * 2
def baseEnd_148050 : Nat := 50680540598833991596091

theorem tailTrace_148050 : CollatzResearch.WordTrace tailWord_148050 prefixEnd_148050 50680540598833991596091 := by
  unfold tailWord_148050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349956778411902443018401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3599884742431739848049069 1349956778411902443018401)
  ·
    refine ⟨1012467583808926832263801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1349956778411902443018401 1012467583808926832263801)
    ·
      refine ⟨759350687856695124197851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1012467583808926832263801 759350687856695124197851)
      ·
        refine ⟨1139026031785042686296777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759350687856695124197851 1139026031785042686296777)
        ·
          refine ⟨854269523838782014722583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1139026031785042686296777 854269523838782014722583)
          ·
            refine ⟨1281404285758173022083875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854269523838782014722583 1281404285758173022083875)
            ·
              refine ⟨1922106428637259533125813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281404285758173022083875 1922106428637259533125813)
              ·
                refine ⟨180197477684743081230545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1922106428637259533125813 180197477684743081230545)
                ·
                  refine ⟨135148108263557310922909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180197477684743081230545 135148108263557310922909)
                  ·
                    refine ⟨50680540598833991596091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135148108263557310922909 50680540598833991596091)
                    ·
                      rfl

theorem cell22_148050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_148050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148050 prefixEnd_148050 := by exact prefixLift 148050
  have htrace : WordTrace (prefixWord ++ tailWord_148050) baseStart_148050 baseEnd_148050 := by
    simpa [prefixWord, tailWord_148050, baseEnd_148050] using wordTrace_append hprefix tailTrace_148050
  have hstable : (prefixWord ++ tailWord_148050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148050).length < 2 ^ (prefixWord ++ tailWord_148050).sum := by decide
  have hdescent : baseEnd_148050 < baseStart_148050 := by decide
  rcases family_descends (prefixWord ++ tailWord_148050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148065 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 2, 4]
def baseStart_148065 : Nat := 118140960795 + 148065 * 2 ^ 59
def prefixEnd_148065 : Nat := 4983230072969 + 3 ^ 40 * 148065 * 2
def baseEnd_148065 : Nat := 50685675405378952471045

theorem tailTrace_148065 : CollatzResearch.WordTrace tailWord_148065 prefixEnd_148065 50685675405378952471045 := by
  unfold tailWord_148065
  simp only [CollatzResearch.WordTrace]
  refine ⟨5400374208593267333869649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3600249472395511555913099 5400374208593267333869649)
  ·
    refine ⟨4050280656444950500402237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5400374208593267333869649 4050280656444950500402237)
    ·
      refine ⟨1518855246166856437650839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4050280656444950500402237 1518855246166856437650839)
      ·
        refine ⟨2278282869250284656476259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518855246166856437650839 2278282869250284656476259)
        ·
          refine ⟨3417424303875426984714389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278282869250284656476259 3417424303875426984714389)
          ·
            refine ⟨160191764244160639908487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3417424303875426984714389 160191764244160639908487)
            ·
              refine ⟨240287646366240959862731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160191764244160639908487 240287646366240959862731)
              ·
                refine ⟨360431469549361439794097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240287646366240959862731 360431469549361439794097)
                ·
                  refine ⟨270323602162021079845573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360431469549361439794097 270323602162021079845573)
                  ·
                    refine ⟨50685675405378952471045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270323602162021079845573 50685675405378952471045)
                    ·
                      rfl

theorem cell22_148065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_148065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148065 prefixEnd_148065 := by exact prefixLift 148065
  have htrace : WordTrace (prefixWord ++ tailWord_148065) baseStart_148065 baseEnd_148065 := by
    simpa [prefixWord, tailWord_148065, baseEnd_148065] using wordTrace_append hprefix tailTrace_148065
  have hstable : (prefixWord ++ tailWord_148065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148065).length < 2 ^ (prefixWord ++ tailWord_148065).sum := by decide
  have hdescent : baseEnd_148065 < baseStart_148065 := by decide
  rcases family_descends (prefixWord ++ tailWord_148065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148172 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_148172 : Nat := 118140960795 + 148172 * 2 ^ 59
def prefixEnd_148172 : Nat := 4983230072969 + 3 ^ 40 * 148172 * 2
def baseEnd_148172 : Nat := 50722303692066340045717

theorem tailTrace_148172 : CollatzResearch.WordTrace tailWord_148172 prefixEnd_148172 50722303692066340045717 := by
  unfold tailWord_148172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702138409602812304007385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3602851212803749738676513 2702138409602812304007385)
  ·
    refine ⟨2026603807202109228005539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2702138409602812304007385 2026603807202109228005539)
    ·
      refine ⟨3039905710803163842008309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026603807202109228005539 3039905710803163842008309)
      ·
        refine ⟨284991160387796610188279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3039905710803163842008309 284991160387796610188279)
        ·
          refine ⟨427486740581694915282419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284991160387796610188279 427486740581694915282419)
          ·
            refine ⟨641230110872542372923629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427486740581694915282419 641230110872542372923629)
            ·
              refine ⟨240461291577203389846361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641230110872542372923629 240461291577203389846361)
              ·
                refine ⟨180345968682902542384771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240461291577203389846361 180345968682902542384771)
                ·
                  refine ⟨270518953024353813577157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180345968682902542384771 270518953024353813577157)
                  ·
                    refine ⟨50722303692066340045717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270518953024353813577157 50722303692066340045717)
                    ·
                      rfl

theorem cell22_148172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_148172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148172 prefixEnd_148172 := by exact prefixLift 148172
  have htrace : WordTrace (prefixWord ++ tailWord_148172) baseStart_148172 baseEnd_148172 := by
    simpa [prefixWord, tailWord_148172, baseEnd_148172] using wordTrace_append hprefix tailTrace_148172
  have hstable : (prefixWord ++ tailWord_148172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148172).length < 2 ^ (prefixWord ++ tailWord_148172).sum := by decide
  have hdescent : baseEnd_148172 < baseStart_148172 := by decide
  rcases family_descends (prefixWord ++ tailWord_148172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148243 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 7]
def baseStart_148243 : Nat := 118140960795 + 148243 * 2 ^ 59
def prefixEnd_148243 : Nat := 4983230072969 + 3 ^ 40 * 148243 * 2
def baseEnd_148243 : Nat := 16915536147681940506833

theorem tailTrace_148243 : CollatzResearch.WordTrace tailWord_148243 prefixEnd_148243 16915536147681940506833 := by
  unfold tailWord_148243
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406866401948403733849383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3604577601298935822566255 5406866401948403733849383)
  ·
    refine ⟨8110299602922605600774075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5406866401948403733849383 8110299602922605600774075)
    ·
      refine ⟨12165449404383908401161113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8110299602922605600774075 12165449404383908401161113)
      ·
        refine ⟨9124087053287931300870835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12165449404383908401161113 9124087053287931300870835)
        ·
          refine ⟨13686130579931896951306253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9124087053287931300870835 13686130579931896951306253)
          ·
            refine ⟨5132298967474461356739845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13686130579931896951306253 5132298967474461356739845)
            ·
              refine ⟨962306056401461504388721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5132298967474461356739845 962306056401461504388721)
              ·
                refine ⟨721729542301096128291541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962306056401461504388721 721729542301096128291541)
                ·
                  refine ⟨16915536147681940506833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 721729542301096128291541 16915536147681940506833)
                  ·
                    rfl

theorem cell22_148243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_148243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148243 prefixEnd_148243 := by exact prefixLift 148243
  have htrace : WordTrace (prefixWord ++ tailWord_148243) baseStart_148243 baseEnd_148243 := by
    simpa [prefixWord, tailWord_148243, baseEnd_148243] using wordTrace_append hprefix tailTrace_148243
  have hstable : (prefixWord ++ tailWord_148243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148243).length < 2 ^ (prefixWord ++ tailWord_148243).sum := by decide
  have hdescent : baseEnd_148243 < baseStart_148243 := by decide
  rcases family_descends (prefixWord ++ tailWord_148243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148253 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_148253 : Nat := 118140960795 + 148253 * 2 ^ 59
def prefixEnd_148253 : Nat := 4983230072969 + 3 ^ 40 * 148253 * 2
def baseEnd_148253 : Nat := 50750031647409128770469

theorem tailTrace_148253 : CollatzResearch.WordTrace tailWord_148253 prefixEnd_148253 50750031647409128770469 := by
  unfold tailWord_148253
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407231131912175441713413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3604820754608116961142275 5407231131912175441713413)
  ·
    refine ⟨1013855837233532895321265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5407231131912175441713413 1013855837233532895321265)
    ·
      refine ⟨760391877925149671490949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1013855837233532895321265 760391877925149671490949)
      ·
        refine ⟨142573477110965563404553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 760391877925149671490949 142573477110965563404553)
        ·
          refine ⟨106930107833224172553415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142573477110965563404553 106930107833224172553415)
          ·
            refine ⟨160395161749836258830123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106930107833224172553415 160395161749836258830123)
            ·
              refine ⟨240592742624754388245185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160395161749836258830123 240592742624754388245185)
              ·
                refine ⟨180444556968565791183889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240592742624754388245185 180444556968565791183889)
                ·
                  refine ⟨135333417726424343387917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180444556968565791183889 135333417726424343387917)
                  ·
                    refine ⟨50750031647409128770469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135333417726424343387917 50750031647409128770469)
                    ·
                      rfl

theorem cell22_148253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_148253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148253 prefixEnd_148253 := by exact prefixLift 148253
  have htrace : WordTrace (prefixWord ++ tailWord_148253) baseStart_148253 baseEnd_148253 := by
    simpa [prefixWord, tailWord_148253, baseEnd_148253] using wordTrace_append hprefix tailTrace_148253
  have hstable : (prefixWord ++ tailWord_148253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148253).length < 2 ^ (prefixWord ++ tailWord_148253).sum := by decide
  have hdescent : baseEnd_148253 < baseStart_148253 := by decide
  rcases family_descends (prefixWord ++ tailWord_148253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148264 : List Nat := [2, 1, 5, 1, 1, 1, 1, 6, 1, 3]
def baseStart_148264 : Nat := 118140960795 + 148264 * 2 ^ 59
def prefixEnd_148264 : Nat := 4983230072969 + 3 ^ 40 * 148264 * 2
def baseEnd_148264 : Nat := 50753797172208766745435

theorem tailTrace_148264 : CollatzResearch.WordTrace tailWord_148264 prefixEnd_148264 50753797172208766745435 := by
  unfold tailWord_148264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703816167436162160181923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3605088223248216213575897 2703816167436162160181923)
  ·
    refine ⟨4055724251154243240272885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2703816167436162160181923 4055724251154243240272885)
    ·
      refine ⟨380224148545710303775583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4055724251154243240272885 380224148545710303775583)
      ·
        refine ⟨570336222818565455663375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380224148545710303775583 570336222818565455663375)
        ·
          refine ⟨855504334227848183495063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570336222818565455663375 855504334227848183495063)
          ·
            refine ⟨1283256501341772275242595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855504334227848183495063 1283256501341772275242595)
            ·
              refine ⟨1924884752012658412863893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283256501341772275242595 1924884752012658412863893)
              ·
                refine ⟨90228972750593363102995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1924884752012658412863893 90228972750593363102995)
                ·
                  refine ⟨135343459125890044654493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90228972750593363102995 135343459125890044654493)
                  ·
                    refine ⟨50753797172208766745435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135343459125890044654493 50753797172208766745435)
                    ·
                      rfl

theorem cell22_148264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_148264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148264 prefixEnd_148264 := by exact prefixLift 148264
  have htrace : WordTrace (prefixWord ++ tailWord_148264) baseStart_148264 baseEnd_148264 := by
    simpa [prefixWord, tailWord_148264, baseEnd_148264] using wordTrace_append hprefix tailTrace_148264
  have hstable : (prefixWord ++ tailWord_148264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148264).length < 2 ^ (prefixWord ++ tailWord_148264).sum := by decide
  have hdescent : baseEnd_148264 < baseStart_148264 := by decide
  rcases family_descends (prefixWord ++ tailWord_148264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148275 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 2, 5]
def baseStart_148275 : Nat := 118140960795 + 148275 * 2 ^ 59
def prefixEnd_148275 : Nat := 4983230072969 + 3 ^ 40 * 148275 * 2
def baseEnd_148275 : Nat := 50757562697008404720401

theorem tailTrace_148275 : CollatzResearch.WordTrace tailWord_148275 prefixEnd_148275 50757562697008404720401 := by
  unfold tailWord_148275
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408033537832473199014279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3605355691888315466009519 5408033537832473199014279)
  ·
    refine ⟨8112050306748709798521419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5408033537832473199014279 8112050306748709798521419)
    ·
      refine ⟨12168075460123064697782129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8112050306748709798521419 12168075460123064697782129)
      ·
        refine ⟨9126056595092298523336597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12168075460123064697782129 9126056595092298523336597)
        ·
          refine ⟨427783902894951493281403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9126056595092298523336597 427783902894951493281403)
          ·
            refine ⟨641675854342427239922105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427783902894951493281403 641675854342427239922105)
            ·
              refine ⟨481256890756820429941579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641675854342427239922105 481256890756820429941579)
              ·
                refine ⟨721885336135230644912369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481256890756820429941579 721885336135230644912369)
                ·
                  refine ⟨541414002101422983684277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721885336135230644912369 541414002101422983684277)
                  ·
                    refine ⟨50757562697008404720401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 541414002101422983684277 50757562697008404720401)
                    ·
                      rfl

theorem cell22_148275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_148275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148275 prefixEnd_148275 := by exact prefixLift 148275
  have htrace : WordTrace (prefixWord ++ tailWord_148275) baseStart_148275 baseEnd_148275 := by
    simpa [prefixWord, tailWord_148275, baseEnd_148275] using wordTrace_append hprefix tailTrace_148275
  have hstable : (prefixWord ++ tailWord_148275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148275).length < 2 ^ (prefixWord ++ tailWord_148275).sum := by decide
  have hdescent : baseEnd_148275 < baseStart_148275 := by decide
  rcases family_descends (prefixWord ++ tailWord_148275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148410 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_148410 : Nat := 118140960795 + 148410 * 2 ^ 59
def prefixEnd_148410 : Nat := 4983230072969 + 3 ^ 40 * 148410 * 2
def baseEnd_148410 : Nat := 50803775955913052594987

theorem tailTrace_148410 : CollatzResearch.WordTrace tailWord_148410 prefixEnd_148410 50803775955913052594987 := by
  unfold tailWord_148410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353239348085847813794671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3608638261562260836785789 1353239348085847813794671)
  ·
    refine ⟨2029859022128771720692007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1353239348085847813794671 2029859022128771720692007)
    ·
      refine ⟨3044788533193157581038011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029859022128771720692007 3044788533193157581038011)
      ·
        refine ⟨4567182799789736371557017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3044788533193157581038011 4567182799789736371557017)
        ·
          refine ⟨3425387099842302278667763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567182799789736371557017 3425387099842302278667763)
          ·
            refine ⟨5138080649763453418001645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425387099842302278667763 5138080649763453418001645)
            ·
              refine ⟨1926780243661295031750617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5138080649763453418001645 1926780243661295031750617)
              ·
                refine ⟨1445085182745971273812963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926780243661295031750617 1445085182745971273812963)
                ·
                  refine ⟨2167627774118956910719445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445085182745971273812963 2167627774118956910719445)
                  ·
                    refine ⟨50803775955913052594987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2167627774118956910719445 50803775955913052594987)
                    ·
                      rfl

theorem cell22_148410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_148410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148410 prefixEnd_148410 := by exact prefixLift 148410
  have htrace : WordTrace (prefixWord ++ tailWord_148410) baseStart_148410 baseEnd_148410 := by
    simpa [prefixWord, tailWord_148410, baseEnd_148410] using wordTrace_append hprefix tailTrace_148410
  have hstable : (prefixWord ++ tailWord_148410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148410).length < 2 ^ (prefixWord ++ tailWord_148410).sum := by decide
  have hdescent : baseEnd_148410 < baseStart_148410 := by decide
  rcases family_descends (prefixWord ++ tailWord_148410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148416 : List Nat := [2, 1, 1, 2, 3, 4, 2, 3, 1, 3]
def baseStart_148416 : Nat := 118140960795 + 148416 * 2 ^ 59
def prefixEnd_148416 : Nat := 4983230072969 + 3 ^ 40 * 148416 * 2
def baseEnd_148416 : Nat := 50805829878531036944969

theorem tailTrace_148416 : CollatzResearch.WordTrace tailWord_148416 prefixEnd_148416 50805829878531036944969 := by
  unfold tailWord_148416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706588115160827139948551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3608784153547769519931401 2706588115160827139948551)
  ·
    refine ⟨4059882172741240709922827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2706588115160827139948551 4059882172741240709922827)
    ·
      refine ⟨6089823259111861064884241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059882172741240709922827 6089823259111861064884241)
      ·
        refine ⟨4567367444333895798663181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6089823259111861064884241 4567367444333895798663181)
        ·
          refine ⟨1712762791625210924498693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4567367444333895798663181 1712762791625210924498693)
          ·
            refine ⟨321143023429727048343505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1712762791625210924498693 321143023429727048343505)
            ·
              refine ⟨240857267572295286257629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321143023429727048343505 240857267572295286257629)
              ·
                refine ⟨90321475339610732346611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240857267572295286257629 90321475339610732346611)
                ·
                  refine ⟨135482213009416098519917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90321475339610732346611 135482213009416098519917)
                  ·
                    refine ⟨50805829878531036944969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135482213009416098519917 50805829878531036944969)
                    ·
                      rfl

theorem cell22_148416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 3].length) (baseStart_148416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148416 prefixEnd_148416 := by exact prefixLift 148416
  have htrace : WordTrace (prefixWord ++ tailWord_148416) baseStart_148416 baseEnd_148416 := by
    simpa [prefixWord, tailWord_148416, baseEnd_148416] using wordTrace_append hprefix tailTrace_148416
  have hstable : (prefixWord ++ tailWord_148416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148416).length < 2 ^ (prefixWord ++ tailWord_148416).sum := by decide
  have hdescent : baseEnd_148416 < baseStart_148416 := by decide
  rcases family_descends (prefixWord ++ tailWord_148416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148491 : List Nat := [1, 1, 1, 1, 6, 3, 3, 2, 4]
def baseStart_148491 : Nat := 118140960795 + 148491 * 2 ^ 59
def prefixEnd_148491 : Nat := 4983230072969 + 3 ^ 40 * 148491 * 2
def baseEnd_148491 : Nat := 16943834637085280439913

theorem tailTrace_148491 : CollatzResearch.WordTrace tailWord_148491 prefixEnd_148491 16943834637085280439913 := by
  unfold tailWord_148491
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415911705049942088877327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3610607803366628059251551 5415911705049942088877327)
  ·
    refine ⟨8123867557574913133315991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5415911705049942088877327 8123867557574913133315991)
    ·
      refine ⟨12185801336362369699973987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8123867557574913133315991 12185801336362369699973987)
      ·
        refine ⟨18278702004543554549960981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12185801336362369699973987 18278702004543554549960981)
        ·
          refine ⟨856814156462979119529421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18278702004543554549960981 856814156462979119529421)
          ·
            refine ⟨321305308673617169823533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 856814156462979119529421 321305308673617169823533)
            ·
              refine ⟨120489490752606438683825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321305308673617169823533 120489490752606438683825)
              ·
                refine ⟨90367118064454829012869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120489490752606438683825 90367118064454829012869)
                ·
                  refine ⟨16943834637085280439913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90367118064454829012869 16943834637085280439913)
                  ·
                    rfl

theorem cell22_148491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 4].length) (baseStart_148491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148491 prefixEnd_148491 := by exact prefixLift 148491
  have htrace : WordTrace (prefixWord ++ tailWord_148491) baseStart_148491 baseEnd_148491 := by
    simpa [prefixWord, tailWord_148491, baseEnd_148491] using wordTrace_append hprefix tailTrace_148491
  have hstable : (prefixWord ++ tailWord_148491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148491).length < 2 ^ (prefixWord ++ tailWord_148491).sum := by decide
  have hdescent : baseEnd_148491 < baseStart_148491 := by decide
  rcases family_descends (prefixWord ++ tailWord_148491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148519 : List Nat := [1, 1, 7, 1, 1, 1, 2, 8]
def baseStart_148519 : Nat := 118140960795 + 148519 * 2 ^ 59
def prefixEnd_148519 : Nat := 4983230072969 + 3 ^ 40 * 148519 * 2
def baseEnd_148519 : Nat := 5649009875941455735517

theorem tailTrace_148519 : CollatzResearch.WordTrace tailWord_148519 prefixEnd_148519 5649009875941455735517 := by
  unfold tailWord_148519
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416932948948502870896611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3611288632632335247264407 5416932948948502870896611)
  ·
    refine ⟨8125399423422754306344917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5416932948948502870896611 8125399423422754306344917)
    ·
      refine ⟨190439048986470804054959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8125399423422754306344917 190439048986470804054959)
      ·
        refine ⟨285658573479706206082439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190439048986470804054959 285658573479706206082439)
        ·
          refine ⟨428487860219559309123659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285658573479706206082439 428487860219559309123659)
          ·
            refine ⟨642731790329338963685489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428487860219559309123659 642731790329338963685489)
            ·
              refine ⟨482048842747004222764117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642731790329338963685489 482048842747004222764117)
              ·
                refine ⟨5649009875941455735517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 482048842747004222764117 5649009875941455735517)
                ·
                  rfl

theorem cell22_148519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 8].length) (baseStart_148519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148519 prefixEnd_148519 := by exact prefixLift 148519
  have htrace : WordTrace (prefixWord ++ tailWord_148519) baseStart_148519 baseEnd_148519 := by
    simpa [prefixWord, tailWord_148519, baseEnd_148519] using wordTrace_append hprefix tailTrace_148519
  have hstable : (prefixWord ++ tailWord_148519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148519).length < 2 ^ (prefixWord ++ tailWord_148519).sum := by decide
  have hdescent : baseEnd_148519 < baseStart_148519 := by decide
  rcases family_descends (prefixWord ++ tailWord_148519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148564 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 5]
def baseStart_148564 : Nat := 118140960795 + 148564 * 2 ^ 59
def prefixEnd_148564 : Nat := 4983230072969 + 3 ^ 40 * 148564 * 2
def baseEnd_148564 : Nat := 16952164434369328081505

theorem tailTrace_148564 : CollatzResearch.WordTrace tailWord_148564 prefixEnd_148564 16952164434369328081505 := by
  unfold tailWord_148564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709287116892737778142373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3612382822523650370856497 2709287116892737778142373)
  ·
    refine ⟨507991334417388333401695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2709287116892737778142373 507991334417388333401695)
    ·
      refine ⟨761987001626082500102543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507991334417388333401695 761987001626082500102543)
      ·
        refine ⟨1142980502439123750153815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761987001626082500102543 1142980502439123750153815)
        ·
          refine ⟨1714470753658685625230723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142980502439123750153815 1714470753658685625230723)
          ·
            refine ⟨2571706130488028437846085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714470753658685625230723 2571706130488028437846085)
            ·
              refine ⟨482194899466505332096141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2571706130488028437846085 482194899466505332096141)
              ·
                refine ⟨180823087299939499536053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482194899466505332096141 180823087299939499536053)
                ·
                  refine ⟨16952164434369328081505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180823087299939499536053 16952164434369328081505)
                  ·
                    rfl

theorem cell22_148564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_148564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148564 prefixEnd_148564 := by exact prefixLift 148564
  have htrace : WordTrace (prefixWord ++ tailWord_148564) baseStart_148564 baseEnd_148564 := by
    simpa [prefixWord, tailWord_148564, baseEnd_148564] using wordTrace_append hprefix tailTrace_148564
  have hstable : (prefixWord ++ tailWord_148564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148564).length < 2 ^ (prefixWord ++ tailWord_148564).sum := by decide
  have hdescent : baseEnd_148564 < baseStart_148564 := by decide
  rcases family_descends (prefixWord ++ tailWord_148564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148592 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 8]
def baseStart_148592 : Nat := 118140960795 + 148592 * 2 ^ 59
def prefixEnd_148592 : Nat := 4983230072969 + 3 ^ 40 * 148592 * 2
def baseEnd_148592 : Nat := 16955359425108414848143

theorem tailTrace_148592 : CollatzResearch.WordTrace tailWord_148592 prefixEnd_148592 16955359425108414848143 := by
  unfold tailWord_148592
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709797738842018169152015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3613063651789357558869353 2709797738842018169152015)
  ·
    refine ⟨4064696608263027253728023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2709797738842018169152015 4064696608263027253728023)
    ·
      refine ⟨6097044912394540880592035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4064696608263027253728023 6097044912394540880592035)
      ·
        refine ⟨9145567368591811320888053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097044912394540880592035 9145567368591811320888053)
        ·
          refine ⟨857396940805482311333255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9145567368591811320888053 857396940805482311333255)
          ·
            refine ⟨1286095411208223466999883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857396940805482311333255 1286095411208223466999883)
            ·
              refine ⟨1929143116812335200499825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286095411208223466999883 1929143116812335200499825)
              ·
                refine ⟨1446857337609251400374869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929143116812335200499825 1446857337609251400374869)
                ·
                  refine ⟨16955359425108414848143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1446857337609251400374869 16955359425108414848143)
                  ·
                    rfl

theorem cell22_148592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_148592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148592 prefixEnd_148592 := by exact prefixLift 148592
  have htrace : WordTrace (prefixWord ++ tailWord_148592) baseStart_148592 baseEnd_148592 := by
    simpa [prefixWord, tailWord_148592, baseEnd_148592] using wordTrace_append hprefix tailTrace_148592
  have hstable : (prefixWord ++ tailWord_148592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148592).length < 2 ^ (prefixWord ++ tailWord_148592).sum := by decide
  have hdescent : baseEnd_148592 < baseStart_148592 := by decide
  rcases family_descends (prefixWord ++ tailWord_148592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148609 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 6]
def baseStart_148609 : Nat := 118140960795 + 148609 * 2 ^ 59
def prefixEnd_148609 : Nat := 4983230072969 + 3 ^ 40 * 148609 * 2
def baseEnd_148609 : Nat := 16957299240914288956459

theorem tailTrace_148609 : CollatzResearch.WordTrace tailWord_148609 prefixEnd_148609 16957299240914288956459 := by
  unfold tailWord_148609
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420215518622448241672881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3613477012414965494448587 5420215518622448241672881)
  ·
    refine ⟨4065161638966836181254661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5420215518622448241672881 4065161638966836181254661)
    ·
      refine ⟨762217807306281783985249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4065161638966836181254661 762217807306281783985249)
      ·
        refine ⟨571663355479711337988937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 762217807306281783985249 571663355479711337988937)
        ·
          refine ⟨428747516609783503491703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571663355479711337988937 428747516609783503491703)
          ·
            refine ⟨643121274914675255237555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428747516609783503491703 643121274914675255237555)
            ·
              refine ⟨964681912372012882856333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643121274914675255237555 964681912372012882856333)
              ·
                refine ⟨361755717139504831071125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964681912372012882856333 361755717139504831071125)
                ·
                  refine ⟨16957299240914288956459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 361755717139504831071125 16957299240914288956459)
                  ·
                    rfl

theorem cell22_148609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_148609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148609 prefixEnd_148609 := by exact prefixLift 148609
  have htrace : WordTrace (prefixWord ++ tailWord_148609) baseStart_148609 baseEnd_148609 := by
    simpa [prefixWord, tailWord_148609, baseEnd_148609] using wordTrace_append hprefix tailTrace_148609
  have hstable : (prefixWord ++ tailWord_148609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148609).length < 2 ^ (prefixWord ++ tailWord_148609).sum := by decide
  have hdescent : baseEnd_148609 < baseStart_148609 := by decide
  rcases family_descends (prefixWord ++ tailWord_148609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148716 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 5]
def baseStart_148716 : Nat := 118140960795 + 148716 * 2 ^ 59
def prefixEnd_148716 : Nat := 4983230072969 + 3 ^ 40 * 148716 * 2
def baseEnd_148716 : Nat := 16969508669810084814683

theorem tailTrace_148716 : CollatzResearch.WordTrace tailWord_148716 prefixEnd_148716 16969508669810084814683 := by
  unfold tailWord_148716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712059064617402757909001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3616078752823203677212001 2712059064617402757909001)
  ·
    refine ⟨2034044298463052068431751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2712059064617402757909001 2034044298463052068431751)
    ·
      refine ⟨3051066447694578102647627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2034044298463052068431751 3051066447694578102647627)
      ·
        refine ⟨4576599671541867153971441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051066447694578102647627 4576599671541867153971441)
        ·
          refine ⟨3432449753656400365478581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4576599671541867153971441 3432449753656400365478581)
          ·
            refine ⟨321792164405287534263617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3432449753656400365478581 321792164405287534263617)
            ·
              refine ⟨241344123303965650697713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321792164405287534263617 241344123303965650697713)
              ·
                refine ⟨181008092477974238023285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241344123303965650697713 181008092477974238023285)
                ·
                  refine ⟨16969508669810084814683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181008092477974238023285 16969508669810084814683)
                  ·
                    rfl

theorem cell22_148716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_148716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148716 prefixEnd_148716 := by exact prefixLift 148716
  have htrace : WordTrace (prefixWord ++ tailWord_148716) baseStart_148716 baseEnd_148716 := by
    simpa [prefixWord, tailWord_148716, baseEnd_148716] using wordTrace_append hprefix tailTrace_148716
  have hstable : (prefixWord ++ tailWord_148716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148716).length < 2 ^ (prefixWord ++ tailWord_148716).sum := by decide
  have hdescent : baseEnd_148716 < baseStart_148716 := by decide
  rcases family_descends (prefixWord ++ tailWord_148716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148729 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_148729 : Nat := 118140960795 + 148729 * 2 ^ 59
def prefixEnd_148729 : Nat := 4983230072969 + 3 ^ 40 * 148729 * 2
def baseEnd_148729 : Nat := 50912976175102553869009

theorem tailTrace_148729 : CollatzResearch.WordTrace tailWord_148729 prefixEnd_148729 50912976175102553869009 := by
  unfold tailWord_148729
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424592278187708736041241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3616394852125139157360827 5424592278187708736041241)
  ·
    refine ⟨4068444208640781552030931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5424592278187708736041241 4068444208640781552030931)
    ·
      refine ⟨6102666312961172328046397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4068444208640781552030931 6102666312961172328046397)
      ·
        refine ⟨2288499867360439623017399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6102666312961172328046397 2288499867360439623017399)
        ·
          refine ⟨3432749801040659434526099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288499867360439623017399 3432749801040659434526099)
          ·
            refine ⟨5149124701560989151789149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432749801040659434526099 5149124701560989151789149)
            ·
              refine ⟨1930921763085370931920931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5149124701560989151789149 1930921763085370931920931)
              ·
                refine ⟨2896382644628056397881397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930921763085370931920931 2896382644628056397881397)
                ·
                  refine ⟨271535872933880287301381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896382644628056397881397 271535872933880287301381)
                  ·
                    refine ⟨50912976175102553869009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271535872933880287301381 50912976175102553869009)
                    ·
                      rfl

theorem cell22_148729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_148729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148729 prefixEnd_148729 := by exact prefixLift 148729
  have htrace : WordTrace (prefixWord ++ tailWord_148729) baseStart_148729 baseEnd_148729 := by
    simpa [prefixWord, tailWord_148729, baseEnd_148729] using wordTrace_append hprefix tailTrace_148729
  have hstable : (prefixWord ++ tailWord_148729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148729).length < 2 ^ (prefixWord ++ tailWord_148729).sum := by decide
  have hdescent : baseEnd_148729 < baseStart_148729 := by decide
  rcases family_descends (prefixWord ++ tailWord_148729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148746 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_148746 : Nat := 118140960795 + 148746 * 2 ^ 59
def prefixEnd_148746 : Nat := 4983230072969 + 3 ^ 40 * 148746 * 2
def baseEnd_148746 : Nat := 50918795622520176193957

theorem tailTrace_148746 : CollatzResearch.WordTrace tailWord_148746 prefixEnd_148746 50918795622520176193957 := by
  unfold tailWord_148746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356303079781530159852523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3616808212750747092940061 1356303079781530159852523)
  ·
    refine ⟨2034454619672295239778785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1356303079781530159852523 2034454619672295239778785)
    ·
      refine ⟨1525840964754221429834089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2034454619672295239778785 1525840964754221429834089)
      ·
        refine ⟨1144380723565666072375567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1525840964754221429834089 1144380723565666072375567)
        ·
          refine ⟨1716571085348499108563351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144380723565666072375567 1716571085348499108563351)
          ·
            refine ⟨2574856628022748662845027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716571085348499108563351 2574856628022748662845027)
            ·
              refine ⟨3862284942034122994267541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574856628022748662845027 3862284942034122994267541)
              ·
                refine ⟨181044606657849515356291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3862284942034122994267541 181044606657849515356291)
                ·
                  refine ⟨271566909986774273034437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181044606657849515356291 271566909986774273034437)
                  ·
                    refine ⟨50918795622520176193957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271566909986774273034437 50918795622520176193957)
                    ·
                      rfl

theorem cell22_148746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_148746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148746 prefixEnd_148746 := by exact prefixLift 148746
  have htrace : WordTrace (prefixWord ++ tailWord_148746) baseStart_148746 baseEnd_148746 := by
    simpa [prefixWord, tailWord_148746, baseEnd_148746] using wordTrace_append hprefix tailTrace_148746
  have hstable : (prefixWord ++ tailWord_148746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148746).length < 2 ^ (prefixWord ++ tailWord_148746).sum := by decide
  have hdescent : baseEnd_148746 < baseStart_148746 := by decide
  rcases family_descends (prefixWord ++ tailWord_148746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148754 : List Nat := [3, 2, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_148754 : Nat := 118140960795 + 148754 * 2 ^ 59
def prefixEnd_148754 : Nat := 4983230072969 + 3 ^ 40 * 148754 * 2
def baseEnd_148754 : Nat := 50921534186010821993933

theorem tailTrace_148754 : CollatzResearch.WordTrace tailWord_148754 prefixEnd_148754 50921534186010821993933 := by
  unfold tailWord_148754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356376025774284501425329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3617002735398092003800877 1356376025774284501425329)
  ·
    refine ⟨1017282019330713376068997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1356376025774284501425329 1017282019330713376068997)
    ·
      refine ⟨190740378624508758012937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1017282019330713376068997 190740378624508758012937)
      ·
        refine ⟨143055283968381568509703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190740378624508758012937 143055283968381568509703)
        ·
          refine ⟨214582925952572352764555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143055283968381568509703 214582925952572352764555)
          ·
            refine ⟨321874388928858529146833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214582925952572352764555 321874388928858529146833)
            ·
              refine ⟨241405791696643896860125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321874388928858529146833 241405791696643896860125)
              ·
                refine ⟨90527171886241461322547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241405791696643896860125 90527171886241461322547)
                ·
                  refine ⟨135790757829362191983821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90527171886241461322547 135790757829362191983821)
                  ·
                    refine ⟨50921534186010821993933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135790757829362191983821 50921534186010821993933)
                    ·
                      rfl

theorem cell22_148754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_148754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148754 prefixEnd_148754 := by exact prefixLift 148754
  have htrace : WordTrace (prefixWord ++ tailWord_148754) baseStart_148754 baseEnd_148754 := by
    simpa [prefixWord, tailWord_148754, baseEnd_148754] using wordTrace_append hprefix tailTrace_148754
  have hstable : (prefixWord ++ tailWord_148754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148754).length < 2 ^ (prefixWord ++ tailWord_148754).sum := by decide
  have hdescent : baseEnd_148754 < baseStart_148754 := by decide
  rcases family_descends (prefixWord ++ tailWord_148754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148778 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_148778 : Nat := 118140960795 + 148778 * 2 ^ 59
def prefixEnd_148778 : Nat := 4983230072969 + 3 ^ 40 * 148778 * 2
def baseEnd_148778 : Nat := 16976583292160919797953

theorem tailTrace_148778 : CollatzResearch.WordTrace tailWord_148778 prefixEnd_148778 16976583292160919797953 := by
  unfold tailWord_148778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356594863752547526143747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3617586303340126736383325 1356594863752547526143747)
  ·
    refine ⟨2034892295628821289215621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1356594863752547526143747 2034892295628821289215621)
    ·
      refine ⟨381542305430403991727929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2034892295628821289215621 381542305430403991727929)
      ·
        refine ⟨286156729072802993795947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381542305430403991727929 286156729072802993795947)
        ·
          refine ⟨429235093609204490693921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286156729072802993795947 429235093609204490693921)
          ·
            refine ⟨321926320206903368020441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429235093609204490693921 321926320206903368020441)
            ·
              refine ⟨241444740155177526015331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321926320206903368020441 241444740155177526015331)
              ·
                refine ⟨362167110232766289022997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241444740155177526015331 362167110232766289022997)
                ·
                  refine ⟨16976583292160919797953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 362167110232766289022997 16976583292160919797953)
                  ·
                    rfl

theorem cell22_148778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_148778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148778 prefixEnd_148778 := by exact prefixLift 148778
  have htrace : WordTrace (prefixWord ++ tailWord_148778) baseStart_148778 baseEnd_148778 := by
    simpa [prefixWord, tailWord_148778, baseEnd_148778] using wordTrace_append hprefix tailTrace_148778
  have hstable : (prefixWord ++ tailWord_148778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148778).length < 2 ^ (prefixWord ++ tailWord_148778).sum := by decide
  have hdescent : baseEnd_148778 < baseStart_148778 := by decide
  rcases family_descends (prefixWord ++ tailWord_148778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148829 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 6]
def baseStart_148829 : Nat := 118140960795 + 148829 * 2 ^ 59
def prefixEnd_148829 : Nat := 4983230072969 + 3 ^ 40 * 148829 * 2
def baseEnd_148829 : Nat := 16982402739578542122901

theorem tailTrace_148829 : CollatzResearch.WordTrace tailWord_148829 prefixEnd_148829 16982402739578542122901 := by
  unfold tailWord_148829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5428239577825425814681541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3618826385216950543121027 5428239577825425814681541)
  ·
    refine ⟨1017794920842267340252789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5428239577825425814681541 1017794920842267340252789)
    ·
      refine ⟨95418273828962563148699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1017794920842267340252789 95418273828962563148699)
      ·
        refine ⟨143127410743443844723049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95418273828962563148699 143127410743443844723049)
        ·
          refine ⟨107345558057582883542287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143127410743443844723049 107345558057582883542287)
          ·
            refine ⟨161018337086374325313431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107345558057582883542287 161018337086374325313431)
            ·
              refine ⟨241527505629561487970147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161018337086374325313431 241527505629561487970147)
              ·
                refine ⟨362291258444342231955221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241527505629561487970147 362291258444342231955221)
                ·
                  refine ⟨16982402739578542122901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 362291258444342231955221 16982402739578542122901)
                  ·
                    rfl

theorem cell22_148829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_148829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148829 prefixEnd_148829 := by exact prefixLift 148829
  have htrace : WordTrace (prefixWord ++ tailWord_148829) baseStart_148829 baseEnd_148829 := by
    simpa [prefixWord, tailWord_148829, baseEnd_148829] using wordTrace_append hprefix tailTrace_148829
  have hstable : (prefixWord ++ tailWord_148829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148829).length < 2 ^ (prefixWord ++ tailWord_148829).sum := by decide
  have hdescent : baseEnd_148829 < baseStart_148829 := by decide
  rcases family_descends (prefixWord ++ tailWord_148829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148896 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 6]
def baseStart_148896 : Nat := 118140960795 + 148896 * 2 ^ 59
def prefixEnd_148896 : Nat := 4983230072969 + 3 ^ 40 * 148896 * 2
def baseEnd_148896 : Nat := 16990047895989928314499

theorem tailTrace_148896 : CollatzResearch.WordTrace tailWord_148896 prefixEnd_148896 16990047895989928314499 := by
  unfold tailWord_148896
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715341634291348128685271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3620455512388464171580361 2715341634291348128685271)
  ·
    refine ⟨4073012451437022193027907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2715341634291348128685271 4073012451437022193027907)
    ·
      refine ⟨6109518677155533289541861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4073012451437022193027907 6109518677155533289541861)
      ·
        refine ⟨1145534751966662491789099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6109518677155533289541861 1145534751966662491789099)
        ·
          refine ⟨1718302127949993737683649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145534751966662491789099 1718302127949993737683649)
          ·
            refine ⟨1288726595962495303262737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1718302127949993737683649 1288726595962495303262737)
            ·
              refine ⟨966544946971871477447053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288726595962495303262737 966544946971871477447053)
              ·
                refine ⟨362454355114451804042645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966544946971871477447053 362454355114451804042645)
                ·
                  refine ⟨16990047895989928314499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 362454355114451804042645 16990047895989928314499)
                  ·
                    rfl

theorem cell22_148896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_148896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148896 prefixEnd_148896 := by exact prefixLift 148896
  have htrace : WordTrace (prefixWord ++ tailWord_148896) baseStart_148896 baseEnd_148896 := by
    simpa [prefixWord, tailWord_148896, baseEnd_148896] using wordTrace_append hprefix tailTrace_148896
  have hstable : (prefixWord ++ tailWord_148896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148896).length < 2 ^ (prefixWord ++ tailWord_148896).sum := by decide
  have hdescent : baseEnd_148896 < baseStart_148896 := by decide
  rcases family_descends (prefixWord ++ tailWord_148896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148898 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_148898 : Nat := 118140960795 + 148898 * 2 ^ 59
def prefixEnd_148898 : Nat := 4983230072969 + 3 ^ 40 * 148898 * 2
def baseEnd_148898 : Nat := 50970828328842446393491

theorem tailTrace_148898 : CollatzResearch.WordTrace tailWord_148898 prefixEnd_148898 50970828328842446393491 := by
  unfold tailWord_148898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357689053643862649735837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3620504143050300399295565 1357689053643862649735837)
  ·
    refine ⟨509133395116448493650939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1357689053643862649735837 509133395116448493650939)
    ·
      refine ⟨763700092674672740476409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509133395116448493650939 763700092674672740476409)
      ·
        refine ⟨572775069506004555357307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 763700092674672740476409 572775069506004555357307)
        ·
          refine ⟨859162604259006833035961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572775069506004555357307 859162604259006833035961)
          ·
            refine ⟨644371953194255124776971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859162604259006833035961 644371953194255124776971)
            ·
              refine ⟨966557929791382687165457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644371953194255124776971 966557929791382687165457)
              ·
                refine ⟨724918447343537015374093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966557929791382687165457 724918447343537015374093)
                ·
                  refine ⟨271844417753826380765285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724918447343537015374093 271844417753826380765285)
                  ·
                    refine ⟨50970828328842446393491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271844417753826380765285 50970828328842446393491)
                    ·
                      rfl

theorem cell22_148898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_148898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148898 prefixEnd_148898 := by exact prefixLift 148898
  have htrace : WordTrace (prefixWord ++ tailWord_148898) baseStart_148898 baseEnd_148898 := by
    simpa [prefixWord, tailWord_148898, baseEnd_148898] using wordTrace_append hprefix tailTrace_148898
  have hstable : (prefixWord ++ tailWord_148898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148898).length < 2 ^ (prefixWord ++ tailWord_148898).sum := by decide
  have hdescent : baseEnd_148898 < baseStart_148898 := by decide
  rcases family_descends (prefixWord ++ tailWord_148898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148932 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_148932 : Nat := 118140960795 + 148932 * 2 ^ 59
def prefixEnd_148932 : Nat := 4983230072969 + 3 ^ 40 * 148932 * 2
def baseEnd_148932 : Nat := 50982467223677691043387

theorem tailTrace_148932 : CollatzResearch.WordTrace tailWord_148932 prefixEnd_148932 50982467223677691043387 := by
  unfold tailWord_148932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715998148226137202840525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3621330864301516270454033 2715998148226137202840525)
  ·
    refine ⟨1018499305584801451065197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2715998148226137202840525 1018499305584801451065197)
    ·
      refine ⟨381937239594300544149449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1018499305584801451065197 381937239594300544149449)
      ·
        refine ⟨286452929695725408112087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381937239594300544149449 286452929695725408112087)
        ·
          refine ⟨429679394543588112168131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286452929695725408112087 429679394543588112168131)
          ·
            refine ⟨644519091815382168252197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429679394543588112168131 644519091815382168252197)
            ·
              refine ⟨120847329715384156547287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 644519091815382168252197 120847329715384156547287)
              ·
                refine ⟨181270994573076234820931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120847329715384156547287 181270994573076234820931)
                ·
                  refine ⟨271906491859614352231397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181270994573076234820931 271906491859614352231397)
                  ·
                    refine ⟨50982467223677691043387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271906491859614352231397 50982467223677691043387)
                    ·
                      rfl

theorem cell22_148932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_148932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148932 prefixEnd_148932 := by exact prefixLift 148932
  have htrace : WordTrace (prefixWord ++ tailWord_148932) baseStart_148932 baseEnd_148932 := by
    simpa [prefixWord, tailWord_148932, baseEnd_148932] using wordTrace_append hprefix tailTrace_148932
  have hstable : (prefixWord ++ tailWord_148932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148932).length < 2 ^ (prefixWord ++ tailWord_148932).sum := by decide
  have hdescent : baseEnd_148932 < baseStart_148932 := by decide
  rcases family_descends (prefixWord ++ tailWord_148932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148986 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_148986 : Nat := 118140960795 + 148986 * 2 ^ 59
def prefixEnd_148986 : Nat := 4983230072969 + 3 ^ 40 * 148986 * 2
def baseEnd_148986 : Nat := 17000317509079850064407

theorem tailTrace_148986 : CollatzResearch.WordTrace tailWord_148986 prefixEnd_148986 17000317509079850064407 := by
  unfold tailWord_148986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358491459564160407036703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3622643892171094418764541 1358491459564160407036703)
  ·
    refine ⟨2037737189346240610555055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1358491459564160407036703 2037737189346240610555055)
    ·
      refine ⟨3056605784019360915832583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037737189346240610555055 3056605784019360915832583)
      ·
        refine ⟨4584908676029041373748875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056605784019360915832583 4584908676029041373748875)
        ·
          refine ⟨6877363014043562060623313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4584908676029041373748875 6877363014043562060623313)
          ·
            refine ⟨5158022260532671545467485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6877363014043562060623313 5158022260532671545467485)
            ·
              refine ⟨1934258347699751829550307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5158022260532671545467485 1934258347699751829550307)
              ·
                refine ⟨2901387521549627744325461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934258347699751829550307 2901387521549627744325461)
                ·
                  refine ⟨17000317509079850064407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2901387521549627744325461 17000317509079850064407)
                  ·
                    rfl

theorem cell22_148986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_148986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148986 prefixEnd_148986 := by exact prefixLift 148986
  have htrace : WordTrace (prefixWord ++ tailWord_148986) baseStart_148986 baseEnd_148986 := by
    simpa [prefixWord, tailWord_148986, baseEnd_148986] using wordTrace_append hprefix tailTrace_148986
  have hstable : (prefixWord ++ tailWord_148986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148986).length < 2 ^ (prefixWord ++ tailWord_148986).sum := by decide
  have hdescent : baseEnd_148986 < baseStart_148986 := by decide
  rcases family_descends (prefixWord ++ tailWord_148986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148998 : List Nat := [6, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_148998 : Nat := 118140960795 + 148998 * 2 ^ 59
def prefixEnd_148998 : Nat := 4983230072969 + 3 ^ 40 * 148998 * 2
def baseEnd_148998 : Nat := 17001686790825172964395

theorem tailTrace_148998 : CollatzResearch.WordTrace tailWord_148998 prefixEnd_148998 17001686790825172964395 := by
  unfold tailWord_148998
  simp only [CollatzResearch.WordTrace]
  refine ⟨169825109819161489924489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3622935676142111785055765 169825109819161489924489)
  ·
    refine ⟨127368832364371117443367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169825109819161489924489 127368832364371117443367)
    ·
      refine ⟨191053248546556676165051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127368832364371117443367 191053248546556676165051)
      ·
        refine ⟨286579872819835014247577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191053248546556676165051 286579872819835014247577)
        ·
          refine ⟨214934904614876260685683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286579872819835014247577 214934904614876260685683)
          ·
            refine ⟨322402356922314391028525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214934904614876260685683 322402356922314391028525)
            ·
              refine ⟨120900883845867896635697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322402356922314391028525 120900883845867896635697)
              ·
                refine ⟨90675662884400922476773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120900883845867896635697 90675662884400922476773)
                ·
                  refine ⟨17001686790825172964395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90675662884400922476773 17001686790825172964395)
                  ·
                    rfl

theorem cell22_148998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_148998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_148998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_148998 prefixEnd_148998 := by exact prefixLift 148998
  have htrace : WordTrace (prefixWord ++ tailWord_148998) baseStart_148998 baseEnd_148998 := by
    simpa [prefixWord, tailWord_148998, baseEnd_148998] using wordTrace_append hprefix tailTrace_148998
  have hstable : (prefixWord ++ tailWord_148998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148998).length < 2 ^ (prefixWord ++ tailWord_148998).sum := by decide
  have hdescent : baseEnd_148998 < baseStart_148998 := by decide
  rcases family_descends (prefixWord ++ tailWord_148998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149095 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 2, 4]
def baseStart_149095 : Nat := 118140960795 + 149095 * 2 ^ 59
def prefixEnd_149095 : Nat := 4983230072969 + 3 ^ 40 * 149095 * 2
def baseEnd_149095 : Nat := 51038265454799599217887

theorem tailTrace_149095 : CollatzResearch.WordTrace tailWord_149095 prefixEnd_149095 51038265454799599217887 := by
  unfold tailWord_149095
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437941394861753243864739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3625294263241168829243159 5437941394861753243864739)
  ·
    refine ⟨8156912092292629865797109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5437941394861753243864739 8156912092292629865797109)
    ·
      refine ⟨764710508652434049918479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8156912092292629865797109 764710508652434049918479)
      ·
        refine ⟨1147065762978651074877719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764710508652434049918479 1147065762978651074877719)
        ·
          refine ⟨1720598644467976612316579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147065762978651074877719 1720598644467976612316579)
          ·
            refine ⟨2580897966701964918474869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720598644467976612316579 2580897966701964918474869)
            ·
              refine ⟨241959184378309211107019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2580897966701964918474869 241959184378309211107019)
              ·
                refine ⟨362938776567463816660529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241959184378309211107019 362938776567463816660529)
                ·
                  refine ⟨272204082425597862495397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362938776567463816660529 272204082425597862495397)
                  ·
                    refine ⟨51038265454799599217887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 272204082425597862495397 51038265454799599217887)
                    ·
                      rfl

theorem cell22_149095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_149095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149095 prefixEnd_149095 := by exact prefixLift 149095
  have htrace : WordTrace (prefixWord ++ tailWord_149095) baseStart_149095 baseEnd_149095 := by
    simpa [prefixWord, tailWord_149095, baseEnd_149095] using wordTrace_append hprefix tailTrace_149095
  have hstable : (prefixWord ++ tailWord_149095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149095).length < 2 ^ (prefixWord ++ tailWord_149095).sum := by decide
  have hdescent : baseEnd_149095 < baseStart_149095 := by decide
  rcases family_descends (prefixWord ++ tailWord_149095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149101 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_149101 : Nat := 118140960795 + 149101 * 2 ^ 59
def prefixEnd_149101 : Nat := 4983230072969 + 3 ^ 40 * 149101 * 2
def baseEnd_149101 : Nat := 51040319377417583567869

theorem tailTrace_149101 : CollatzResearch.WordTrace tailWord_149101 prefixEnd_149101 51040319377417583567869 := by
  unfold tailWord_149101
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438160232840016268583157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3625440155226677512388771 5438160232840016268583157)
  ·
    refine ⟨509827521828751525179671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5438160232840016268583157 509827521828751525179671)
    ·
      refine ⟨764741282743127287769507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509827521828751525179671 764741282743127287769507)
      ·
        refine ⟨1147111924114690931654261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764741282743127287769507 1147111924114690931654261)
        ·
          refine ⟨107541742885752274842587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1147111924114690931654261 107541742885752274842587)
          ·
            refine ⟨161312614328628412263881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107541742885752274842587 161312614328628412263881)
            ·
              refine ⟨120984460746471309197911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161312614328628412263881 120984460746471309197911)
              ·
                refine ⟨181476691119706963796867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120984460746471309197911 181476691119706963796867)
                ·
                  refine ⟨272215036679560445695301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181476691119706963796867 272215036679560445695301)
                  ·
                    refine ⟨51040319377417583567869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 272215036679560445695301 51040319377417583567869)
                    ·
                      rfl

theorem cell22_149101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_149101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149101 prefixEnd_149101 := by exact prefixLift 149101
  have htrace : WordTrace (prefixWord ++ tailWord_149101) baseStart_149101 baseEnd_149101 := by
    simpa [prefixWord, tailWord_149101, baseEnd_149101] using wordTrace_append hprefix tailTrace_149101
  have hstable : (prefixWord ++ tailWord_149101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149101).length < 2 ^ (prefixWord ++ tailWord_149101).sum := by decide
  have hdescent : baseEnd_149101 < baseStart_149101 := by decide
  rcases family_descends (prefixWord ++ tailWord_149101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149110 : List Nat := [5, 1, 1, 2, 2, 2, 9]
def baseStart_149110 : Nat := 118140960795 + 149110 * 2 ^ 59
def prefixEnd_149110 : Nat := 4983230072969 + 3 ^ 40 * 149110 * 2
def baseEnd_149110 : Nat := 1890496305975724447883

theorem tailTrace_149110 : CollatzResearch.WordTrace tailWord_149110 prefixEnd_149110 1890496305975724447883 := by
  unfold tailWord_149110
  simp only [CollatzResearch.WordTrace]
  refine ⟨339905530612963175353799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3625658993204940537107189 339905530612963175353799)
  ·
    refine ⟨509858295919444763030699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 339905530612963175353799 509858295919444763030699)
    ·
      refine ⟨764787443879167144546049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509858295919444763030699 764787443879167144546049)
      ·
        refine ⟨573590582909375358409537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 764787443879167144546049 573590582909375358409537)
        ·
          refine ⟨430192937182031518807153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 573590582909375358409537 430192937182031518807153)
          ·
            refine ⟨322644702886523639105365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430192937182031518807153 322644702886523639105365)
            ·
              refine ⟨1890496305975724447883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 322644702886523639105365 1890496305975724447883)
              ·
                rfl

theorem cell22_149110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 9].length) (baseStart_149110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149110 prefixEnd_149110 := by exact prefixLift 149110
  have htrace : WordTrace (prefixWord ++ tailWord_149110) baseStart_149110 baseEnd_149110 := by
    simpa [prefixWord, tailWord_149110, baseEnd_149110] using wordTrace_append hprefix tailTrace_149110
  have hstable : (prefixWord ++ tailWord_149110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149110).length < 2 ^ (prefixWord ++ tailWord_149110).sum := by decide
  have hdescent : baseEnd_149110 < baseStart_149110 := by decide
  rcases family_descends (prefixWord ++ tailWord_149110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149202 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_149202 : Nat := 118140960795 + 149202 * 2 ^ 59
def prefixEnd_149202 : Nat := 4983230072969 + 3 ^ 40 * 149202 * 2
def baseEnd_149202 : Nat := 51074893741486986792559

theorem tailTrace_149202 : CollatzResearch.WordTrace tailWord_149202 prefixEnd_149202 51074893741486986792559 := by
  unfold tailWord_149202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360461001368527629502465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3627896003649407012006573 1360461001368527629502465)
  ·
    refine ⟨1020345751026395722126849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1360461001368527629502465 1020345751026395722126849)
    ·
      refine ⟨765259313269796791595137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1020345751026395722126849 765259313269796791595137)
      ·
        refine ⟨573944484952347593696353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 765259313269796791595137 573944484952347593696353)
        ·
          refine ⟨430458363714260695272265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 573944484952347593696353 430458363714260695272265)
          ·
            refine ⟨322843772785695521454199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430458363714260695272265 322843772785695521454199)
            ·
              refine ⟨484265659178543282181299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322843772785695521454199 484265659178543282181299)
              ·
                refine ⟨726398488767814923271949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484265659178543282181299 726398488767814923271949)
                ·
                  refine ⟨272399433287930596226981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726398488767814923271949 272399433287930596226981)
                  ·
                    refine ⟨51074893741486986792559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 272399433287930596226981 51074893741486986792559)
                    ·
                      rfl

theorem cell22_149202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_149202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149202 prefixEnd_149202 := by exact prefixLift 149202
  have htrace : WordTrace (prefixWord ++ tailWord_149202) baseStart_149202 baseEnd_149202 := by
    simpa [prefixWord, tailWord_149202, baseEnd_149202] using wordTrace_append hprefix tailTrace_149202
  have hstable : (prefixWord ++ tailWord_149202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149202).length < 2 ^ (prefixWord ++ tailWord_149202).sum := by decide
  have hdescent : baseEnd_149202 < baseStart_149202 := by decide
  rcases family_descends (prefixWord ++ tailWord_149202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149215 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 1, 5]
def baseStart_149215 : Nat := 118140960795 + 149215 * 2 ^ 59
def prefixEnd_149215 : Nat := 4983230072969 + 3 ^ 40 * 149215 * 2
def baseEnd_149215 : Nat := 51079343907159286217519

theorem tailTrace_149215 : CollatzResearch.WordTrace tailWord_149215 prefixEnd_149215 51079343907159286217519 := by
  unfold tailWord_149215
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442318154427013738233099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3628212102951342492155399 5442318154427013738233099)
  ·
    refine ⟨8163477231640520607349649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5442318154427013738233099 8163477231640520607349649)
    ·
      refine ⟨6122607923730390455512237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8163477231640520607349649 6122607923730390455512237)
      ·
        refine ⟨2295977971398896420817089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6122607923730390455512237 2295977971398896420817089)
        ·
          refine ⟨1721983478549172315612817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2295977971398896420817089 1721983478549172315612817)
          ·
            refine ⟨1291487608911879236709613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721983478549172315612817 1291487608911879236709613)
            ·
              refine ⟨484307853341954713766105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1291487608911879236709613 484307853341954713766105)
              ·
                refine ⟨363230890006466035324579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484307853341954713766105 363230890006466035324579)
                ·
                  refine ⟨544846335009699052986869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363230890006466035324579 544846335009699052986869)
                  ·
                    refine ⟨51079343907159286217519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 544846335009699052986869 51079343907159286217519)
                    ·
                      rfl

theorem cell22_149215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_149215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149215 prefixEnd_149215 := by exact prefixLift 149215
  have htrace : WordTrace (prefixWord ++ tailWord_149215) baseStart_149215 baseEnd_149215 := by
    simpa [prefixWord, tailWord_149215, baseEnd_149215] using wordTrace_append hprefix tailTrace_149215
  have hstable : (prefixWord ++ tailWord_149215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149215).length < 2 ^ (prefixWord ++ tailWord_149215).sum := by decide
  have hdescent : baseEnd_149215 < baseStart_149215 := by decide
  rcases family_descends (prefixWord ++ tailWord_149215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149337 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_149337 : Nat := 118140960795 + 149337 * 2 ^ 59
def prefixEnd_149337 : Nat := 4983230072969 + 3 ^ 40 * 149337 * 2
def baseEnd_149337 : Nat := 51121107000391634667145

theorem tailTrace_149337 : CollatzResearch.WordTrace tailWord_149337 prefixEnd_149337 51121107000391634667145 := by
  unfold tailWord_149337
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446767859985028574174265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3631178573323352382782843 5446767859985028574174265)
  ·
    refine ⟨4085075894988771430630699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5446767859985028574174265 4085075894988771430630699)
    ·
      refine ⟨6127613842483157145946049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4085075894988771430630699 6127613842483157145946049)
      ·
        refine ⟨4595710381862367859459537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6127613842483157145946049 4595710381862367859459537)
        ·
          refine ⟨3446782786396775894594653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4595710381862367859459537 3446782786396775894594653)
          ·
            refine ⟨1292543544898790960472995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3446782786396775894594653 1292543544898790960472995)
            ·
              refine ⟨1938815317348186440709493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292543544898790960472995 1938815317348186440709493)
              ·
                refine ⟨181763936001392478816515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1938815317348186440709493 181763936001392478816515)
                ·
                  refine ⟨272645904002088718224773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181763936001392478816515 272645904002088718224773)
                  ·
                    refine ⟨51121107000391634667145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 272645904002088718224773 51121107000391634667145)
                    ·
                      rfl

theorem cell22_149337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_149337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149337 prefixEnd_149337 := by exact prefixLift 149337
  have htrace : WordTrace (prefixWord ++ tailWord_149337) baseStart_149337 baseEnd_149337 := by
    simpa [prefixWord, tailWord_149337, baseEnd_149337] using wordTrace_append hprefix tailTrace_149337
  have hstable : (prefixWord ++ tailWord_149337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149337).length < 2 ^ (prefixWord ++ tailWord_149337).sum := by decide
  have hdescent : baseEnd_149337 < baseStart_149337 := by decide
  rcases family_descends (prefixWord ++ tailWord_149337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149384 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_149384 : Nat := 118140960795 + 149384 * 2 ^ 59
def prefixEnd_149384 : Nat := 4983230072969 + 3 ^ 40 * 149384 * 2
def baseEnd_149384 : Nat := 51137196060899178742001

theorem tailTrace_149384 : CollatzResearch.WordTrace tailWord_149384 prefixEnd_149384 51137196060899178742001 := by
  unfold tailWord_149384
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724241045407377800567603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3632321393876503734090137 2724241045407377800567603)
  ·
    refine ⟨4086361568111066700851405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2724241045407377800567603 4086361568111066700851405)
    ·
      refine ⟨1532385588041650012819277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4086361568111066700851405 1532385588041650012819277)
      ·
        refine ⟨574644595515618754807229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1532385588041650012819277 574644595515618754807229)
        ·
          refine ⟨215491723318357033052711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574644595515618754807229 215491723318357033052711)
          ·
            refine ⟨323237584977535549579067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215491723318357033052711 323237584977535549579067)
            ·
              refine ⟨484856377466303324368601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323237584977535549579067 484856377466303324368601)
              ·
                refine ⟨363642283099727493276451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484856377466303324368601 363642283099727493276451)
                ·
                  refine ⟨545463424649591239914677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363642283099727493276451 545463424649591239914677)
                  ·
                    refine ⟨51137196060899178742001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 545463424649591239914677 51137196060899178742001)
                    ·
                      rfl

theorem cell22_149384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_149384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149384 prefixEnd_149384 := by exact prefixLift 149384
  have htrace : WordTrace (prefixWord ++ tailWord_149384) baseStart_149384 baseEnd_149384 := by
    simpa [prefixWord, tailWord_149384, baseEnd_149384] using wordTrace_append hprefix tailTrace_149384
  have hstable : (prefixWord ++ tailWord_149384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149384).length < 2 ^ (prefixWord ++ tailWord_149384).sum := by decide
  have hdescent : baseEnd_149384 < baseStart_149384 := by decide
  rcases family_descends (prefixWord ++ tailWord_149384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149395 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 4, 7]
def baseStart_149395 : Nat := 118140960795 + 149395 * 2 ^ 59
def prefixEnd_149395 : Nat := 4983230072969 + 3 ^ 40 * 149395 * 2
def baseEnd_149395 : Nat := 51140961585698816716967

theorem tailTrace_149395 : CollatzResearch.WordTrace tailWord_149395 prefixEnd_149395 51140961585698816716967 := by
  unfold tailWord_149395
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448883293774904479785639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3632588862516602986523759 5448883293774904479785639)
  ·
    refine ⟨8173324940662356719678459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5448883293774904479785639 8173324940662356719678459)
    ·
      refine ⟨12259987410993535079517689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8173324940662356719678459 12259987410993535079517689)
      ·
        refine ⟨9194990558245151309638267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12259987410993535079517689 9194990558245151309638267)
        ·
          refine ⟨13792485837367726964457401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9194990558245151309638267 13792485837367726964457401)
          ·
            refine ⟨10344364378025795223343051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13792485837367726964457401 10344364378025795223343051)
            ·
              refine ⟨15516546567038692835014577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10344364378025795223343051 15516546567038692835014577)
              ·
                refine ⟨11637409925279019626260933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15516546567038692835014577 11637409925279019626260933)
                ·
                  refine ⟨2182014360989816179923925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11637409925279019626260933 2182014360989816179923925)
                  ·
                    refine ⟨51140961585698816716967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2182014360989816179923925 51140961585698816716967)
                    ·
                      rfl

theorem cell22_149395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_149395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149395 prefixEnd_149395 := by exact prefixLift 149395
  have htrace : WordTrace (prefixWord ++ tailWord_149395) baseStart_149395 baseEnd_149395 := by
    simpa [prefixWord, tailWord_149395, baseEnd_149395] using wordTrace_append hprefix tailTrace_149395
  have hstable : (prefixWord ++ tailWord_149395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149395).length < 2 ^ (prefixWord ++ tailWord_149395).sum := by decide
  have hdescent : baseEnd_149395 < baseStart_149395 := by decide
  rcases family_descends (prefixWord ++ tailWord_149395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149429 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_149429 : Nat := 118140960795 + 149429 * 2 ^ 59
def prefixEnd_149429 : Nat := 4983230072969 + 3 ^ 40 * 149429 * 2
def baseEnd_149429 : Nat := 51152600480534061366863

theorem tailTrace_149429 : CollatzResearch.WordTrace tailWord_149429 prefixEnd_149429 51152600480534061366863 := by
  unfold tailWord_149429
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450123375651728286523341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3633415583767818857682227 5450123375651728286523341)
  ·
    refine ⟨2043796265869398107446253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5450123375651728286523341 2043796265869398107446253)
    ·
      refine ⟨766423599701024290292345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2043796265869398107446253 766423599701024290292345)
      ·
        refine ⟨574817699775768217719259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 766423599701024290292345 574817699775768217719259)
        ·
          refine ⟨862226549663652326578889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574817699775768217719259 862226549663652326578889)
          ·
            refine ⟨646669912247739244934167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862226549663652326578889 646669912247739244934167)
            ·
              refine ⟨970004868371608867401251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646669912247739244934167 970004868371608867401251)
              ·
                refine ⟨1455007302557413301101877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970004868371608867401251 1455007302557413301101877)
                ·
                  refine ⟨136406934614757496978301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1455007302557413301101877 136406934614757496978301)
                  ·
                    refine ⟨51152600480534061366863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136406934614757496978301 51152600480534061366863)
                    ·
                      rfl

theorem cell22_149429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_149429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149429 prefixEnd_149429 := by exact prefixLift 149429
  have htrace : WordTrace (prefixWord ++ tailWord_149429) baseStart_149429 baseEnd_149429 := by
    simpa [prefixWord, tailWord_149429, baseEnd_149429] using wordTrace_append hprefix tailTrace_149429
  have hstable : (prefixWord ++ tailWord_149429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149429).length < 2 ^ (prefixWord ++ tailWord_149429).sum := by decide
  have hdescent : baseEnd_149429 < baseStart_149429 := by decide
  rcases family_descends (prefixWord ++ tailWord_149429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149472 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_149472 : Nat := 118140960795 + 149472 * 2 ^ 59
def prefixEnd_149472 : Nat := 4983230072969 + 3 ^ 40 * 149472 * 2
def baseEnd_149472 : Nat := 51167320259296282541731

theorem tailTrace_149472 : CollatzResearch.WordTrace tailWord_149472 prefixEnd_149472 51167320259296282541731 := by
  unfold tailWord_149472
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725845857247973315169335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3634461142997297753559113 2725845857247973315169335)
  ·
    refine ⟨4088768785871959972754003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2725845857247973315169335 4088768785871959972754003)
    ·
      refine ⟨6133153178807939959131005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088768785871959972754003 6133153178807939959131005)
      ·
        refine ⟨2299932442052977484674127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6133153178807939959131005 2299932442052977484674127)
        ·
          refine ⟨3449898663079466227011191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299932442052977484674127 3449898663079466227011191)
          ·
            refine ⟨5174847994619199340516787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449898663079466227011191 5174847994619199340516787)
            ·
              refine ⟨7762271991928799010775181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5174847994619199340516787 7762271991928799010775181)
              ·
                refine ⟨2910851996973299629040693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7762271991928799010775181 2910851996973299629040693)
                ·
                  refine ⟨272892374716246840222565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2910851996973299629040693 272892374716246840222565)
                  ·
                    refine ⟨51167320259296282541731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 272892374716246840222565 51167320259296282541731)
                    ·
                      rfl

theorem cell22_149472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_149472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149472 prefixEnd_149472 := by exact prefixLift 149472
  have htrace : WordTrace (prefixWord ++ tailWord_149472) baseStart_149472 baseEnd_149472 := by
    simpa [prefixWord, tailWord_149472, baseEnd_149472] using wordTrace_append hprefix tailTrace_149472
  have hstable : (prefixWord ++ tailWord_149472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149472).length < 2 ^ (prefixWord ++ tailWord_149472).sum := by decide
  have hdescent : baseEnd_149472 < baseStart_149472 := by decide
  rcases family_descends (prefixWord ++ tailWord_149472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149487 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 6]
def baseStart_149487 : Nat := 118140960795 + 149487 * 2 ^ 59
def prefixEnd_149487 : Nat := 4983230072969 + 3 ^ 40 * 149487 * 2
def baseEnd_149487 : Nat := 17057485021947081138895

theorem tailTrace_149487 : CollatzResearch.WordTrace tailWord_149487 prefixEnd_149487 17057485021947081138895 := by
  unfold tailWord_149487
  simp only [CollatzResearch.WordTrace]
  refine ⟨5452238809441604192134715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3634825872961069461423143 5452238809441604192134715)
  ·
    refine ⟨8178358214162406288202073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5452238809441604192134715 8178358214162406288202073)
    ·
      refine ⟨6133768660621804716151555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8178358214162406288202073 6133768660621804716151555)
      ·
        refine ⟨9200652990932707074227333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6133768660621804716151555 9200652990932707074227333)
        ·
          refine ⟨1725122435799882576417625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9200652990932707074227333 1725122435799882576417625)
          ·
            refine ⟨1293841826849911932313219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1725122435799882576417625 1293841826849911932313219)
            ·
              refine ⟨1940762740274867898469829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293841826849911932313219 1940762740274867898469829)
              ·
                refine ⟨363893013801537730963093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1940762740274867898469829 363893013801537730963093)
                ·
                  refine ⟨17057485021947081138895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 363893013801537730963093 17057485021947081138895)
                  ·
                    rfl

theorem cell22_149487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 6].length) (baseStart_149487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149487 prefixEnd_149487 := by exact prefixLift 149487
  have htrace : WordTrace (prefixWord ++ tailWord_149487) baseStart_149487 baseEnd_149487 := by
    simpa [prefixWord, tailWord_149487, baseEnd_149487] using wordTrace_append hprefix tailTrace_149487
  have hstable : (prefixWord ++ tailWord_149487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149487).length < 2 ^ (prefixWord ++ tailWord_149487).sum := by decide
  have hdescent : baseEnd_149487 < baseStart_149487 := by decide
  rcases family_descends (prefixWord ++ tailWord_149487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149504 : List Nat := [2, 1, 1, 2, 1, 1, 1, 9, 4]
def baseStart_149504 : Nat := 118140960795 + 149504 * 2 ^ 59
def prefixEnd_149504 : Nat := 4983230072969 + 3 ^ 40 * 149504 * 2
def baseEnd_149504 : Nat := 17059424837752955247211

theorem tailTrace_149504 : CollatzResearch.WordTrace tailWord_149504 prefixEnd_149504 17059424837752955247211 := by
  unfold tailWord_149504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2726429425190008047751783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3635239233586677397002377 2726429425190008047751783)
  ·
    refine ⟨4089644137785012071627675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2726429425190008047751783 4089644137785012071627675)
    ·
      refine ⟨6134466206677518107441513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4089644137785012071627675 6134466206677518107441513)
      ·
        refine ⟨4600849655008138580581135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6134466206677518107441513 4600849655008138580581135)
        ·
          refine ⟨6901274482512207870871703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4600849655008138580581135 6901274482512207870871703)
          ·
            refine ⟨10351911723768311806307555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6901274482512207870871703 10351911723768311806307555)
            ·
              refine ⟨15527867585652467709461333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10351911723768311806307555 15527867585652467709461333)
              ·
                refine ⟨90983599134682427985125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15527867585652467709461333 90983599134682427985125)
                ·
                  refine ⟨17059424837752955247211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90983599134682427985125 17059424837752955247211)
                  ·
                    rfl

theorem cell22_149504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_149504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149504 prefixEnd_149504 := by exact prefixLift 149504
  have htrace : WordTrace (prefixWord ++ tailWord_149504) baseStart_149504 baseEnd_149504 := by
    simpa [prefixWord, tailWord_149504, baseEnd_149504] using wordTrace_append hprefix tailTrace_149504
  have hstable : (prefixWord ++ tailWord_149504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149504).length < 2 ^ (prefixWord ++ tailWord_149504).sum := by decide
  have hdescent : baseEnd_149504 < baseStart_149504 := by decide
  rcases family_descends (prefixWord ++ tailWord_149504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149540 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_149540 : Nat := 118140960795 + 149540 * 2 ^ 59
def prefixEnd_149540 : Nat := 4983230072969 + 3 ^ 40 * 149540 * 2
def baseEnd_149540 : Nat := 51190598048966771841523

theorem tailTrace_149540 : CollatzResearch.WordTrace tailWord_149540 prefixEnd_149540 51190598048966771841523 := by
  unfold tailWord_149540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2727085939124797121907037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3636114585499729495876049 2727085939124797121907037)
  ·
    refine ⟨1022657227171798920715139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2727085939124797121907037 1022657227171798920715139)
    ·
      refine ⟨1533985840757698381072709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022657227171798920715139 1533985840757698381072709)
      ·
        refine ⟨287622345142068446451133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1533985840757698381072709 287622345142068446451133)
        ·
          refine ⟨107858379428275667419175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287622345142068446451133 107858379428275667419175)
          ·
            refine ⟨161787569142413501128763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107858379428275667419175 161787569142413501128763)
            ·
              refine ⟨242681353713620251693145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161787569142413501128763 242681353713620251693145)
              ·
                refine ⟨182011015285215188769859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242681353713620251693145 182011015285215188769859)
                ·
                  refine ⟨273016522927822783154789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182011015285215188769859 273016522927822783154789)
                  ·
                    refine ⟨51190598048966771841523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 273016522927822783154789 51190598048966771841523)
                    ·
                      rfl

theorem cell22_149540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_149540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149540 prefixEnd_149540 := by exact prefixLift 149540
  have htrace : WordTrace (prefixWord ++ tailWord_149540) baseStart_149540 baseEnd_149540 := by
    simpa [prefixWord, tailWord_149540, baseEnd_149540] using wordTrace_append hprefix tailTrace_149540
  have hstable : (prefixWord ++ tailWord_149540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149540).length < 2 ^ (prefixWord ++ tailWord_149540).sum := by decide
  have hdescent : baseEnd_149540 < baseStart_149540 := by decide
  rcases family_descends (prefixWord ++ tailWord_149540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149566 : List Nat := [4, 2, 1, 3, 3, 9]
def baseStart_149566 : Nat := 118140960795 + 149566 * 2 ^ 59
def prefixEnd_149566 : Nat := 4983230072969 + 3 ^ 40 * 149566 * 2
def baseEnd_149566 : Nat := 632092572596436675203

theorem tailTrace_149566 : CollatzResearch.WordTrace tailWord_149566 prefixEnd_149566 632092572596436675203 := by
  unfold tailWord_149566
  simp only [CollatzResearch.WordTrace]
  refine ⟨681890022019425085532569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3636746784103600456173701 681890022019425085532569)
  ·
    refine ⟨511417516514568814149427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 681890022019425085532569 511417516514568814149427)
    ·
      refine ⟨767126274771853221224141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511417516514568814149427 767126274771853221224141)
      ·
        refine ⟨287672353039444957959053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 767126274771853221224141 287672353039444957959053)
        ·
          refine ⟨107877132389791859234645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287672353039444957959053 107877132389791859234645)
          ·
            refine ⟨632092572596436675203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 107877132389791859234645 632092572596436675203)
            ·
              rfl

theorem cell22_149566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 9].length) (baseStart_149566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149566 prefixEnd_149566 := by exact prefixLift 149566
  have htrace : WordTrace (prefixWord ++ tailWord_149566) baseStart_149566 baseEnd_149566 := by
    simpa [prefixWord, tailWord_149566, baseEnd_149566] using wordTrace_append hprefix tailTrace_149566
  have hstable : (prefixWord ++ tailWord_149566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149566).length < 2 ^ (prefixWord ++ tailWord_149566).sum := by decide
  have hdescent : baseEnd_149566 < baseStart_149566 := by decide
  rcases family_descends (prefixWord ++ tailWord_149566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149594 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_149594 : Nat := 118140960795 + 149594 * 2 ^ 59
def prefixEnd_149594 : Nat := 4983230072969 + 3 ^ 40 * 149594 * 2
def baseEnd_149594 : Nat := 17069694450842876997119

theorem tailTrace_149594 : CollatzResearch.WordTrace tailWord_149594 prefixEnd_149594 17069694450842876997119 := by
  unfold tailWord_149594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364035355013490366569959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3637427613369307644186557 1364035355013490366569959)
  ·
    refine ⟨2046053032520235549854939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1364035355013490366569959 2046053032520235549854939)
    ·
      refine ⟨3069079548780353324782409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046053032520235549854939 3069079548780353324782409)
      ·
        refine ⟨2301809661585264993586807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3069079548780353324782409 2301809661585264993586807)
        ·
          refine ⟨3452714492377897490380211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301809661585264993586807 3452714492377897490380211)
          ·
            refine ⟨5179071738566846235570317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452714492377897490380211 5179071738566846235570317)
            ·
              refine ⟨1942151901962567338338869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5179071738566846235570317 1942151901962567338338869)
              ·
                refine ⟨182076740808990687969269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1942151901962567338338869 182076740808990687969269)
                ·
                  refine ⟨17069694450842876997119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182076740808990687969269 17069694450842876997119)
                  ·
                    rfl

theorem cell22_149594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_149594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149594 prefixEnd_149594 := by exact prefixLift 149594
  have htrace : WordTrace (prefixWord ++ tailWord_149594) baseStart_149594 baseEnd_149594 := by
    simpa [prefixWord, tailWord_149594, baseEnd_149594] using wordTrace_append hprefix tailTrace_149594
  have hstable : (prefixWord ++ tailWord_149594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149594).length < 2 ^ (prefixWord ++ tailWord_149594).sum := by decide
  have hdescent : baseEnd_149594 < baseStart_149594 := by decide
  rcases family_descends (prefixWord ++ tailWord_149594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149639 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 6]
def baseStart_149639 : Nat := 118140960795 + 149639 * 2 ^ 59
def prefixEnd_149639 : Nat := 4983230072969 + 3 ^ 40 * 149639 * 2
def baseEnd_149639 : Nat := 17074829257387837872073

theorem tailTrace_149639 : CollatzResearch.WordTrace tailWord_149639 prefixEnd_149639 17074829257387837872073 := by
  unfold tailWord_149639
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457782704890934151667971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3638521803260622767778647 5457782704890934151667971)
  ·
    refine ⟨8186674057336401227501957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5457782704890934151667971 8186674057336401227501957)
    ·
      refine ⟨1535001385750575230156617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8186674057336401227501957 1535001385750575230156617)
      ·
        refine ⟨1151251039312931422617463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1535001385750575230156617 1151251039312931422617463)
        ·
          refine ⟨1726876558969397133926195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151251039312931422617463 1726876558969397133926195)
          ·
            refine ⟨2590314838454095700889293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726876558969397133926195 2590314838454095700889293)
            ·
              refine ⟨971368064420285887833485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2590314838454095700889293 971368064420285887833485)
              ·
                refine ⟨364263024157607207937557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971368064420285887833485 364263024157607207937557)
                ·
                  refine ⟨17074829257387837872073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 364263024157607207937557 17074829257387837872073)
                  ·
                    rfl

theorem cell22_149639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 6].length) (baseStart_149639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149639 prefixEnd_149639 := by exact prefixLift 149639
  have htrace : WordTrace (prefixWord ++ tailWord_149639) baseStart_149639 baseEnd_149639 := by
    simpa [prefixWord, tailWord_149639, baseEnd_149639] using wordTrace_append hprefix tailTrace_149639
  have hstable : (prefixWord ++ tailWord_149639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149639).length < 2 ^ (prefixWord ++ tailWord_149639).sum := by decide
  have hdescent : baseEnd_149639 < baseStart_149639 := by decide
  rcases family_descends (prefixWord ++ tailWord_149639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149669 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_149669 : Nat := 118140960795 + 149669 * 2 ^ 59
def prefixEnd_149669 : Nat := 4983230072969 + 3 ^ 40 * 149669 * 2
def baseEnd_149669 : Nat := 51234757385253435366127

theorem tailTrace_149669 : CollatzResearch.WordTrace tailWord_149669 prefixEnd_149669 51234757385253435366127 := by
  unfold tailWord_149669
  simp only [CollatzResearch.WordTrace]
  refine ⟨5458876894782249275260061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3639251263188166183506707 5458876894782249275260061)
  ·
    refine ⟨2047078835543343478222523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5458876894782249275260061 2047078835543343478222523)
    ·
      refine ⟨3070618253315015217333785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047078835543343478222523 3070618253315015217333785)
      ·
        refine ⟨2302963689986261413000339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3070618253315015217333785 2302963689986261413000339)
        ·
          refine ⟨3454445534979392119500509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302963689986261413000339 3454445534979392119500509)
          ·
            refine ⟨1295417075617272044812691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3454445534979392119500509 1295417075617272044812691)
            ·
              refine ⟨1943125613425908067219037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295417075617272044812691 1943125613425908067219037)
              ·
                refine ⟨728672105034715525207139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1943125613425908067219037 728672105034715525207139)
                ·
                  refine ⟨1093008157552073287810709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728672105034715525207139 1093008157552073287810709)
                  ·
                    refine ⟨51234757385253435366127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1093008157552073287810709 51234757385253435366127)
                    ·
                      rfl

theorem cell22_149669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_149669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149669 prefixEnd_149669 := by exact prefixLift 149669
  have htrace : WordTrace (prefixWord ++ tailWord_149669) baseStart_149669 baseEnd_149669 := by
    simpa [prefixWord, tailWord_149669, baseEnd_149669] using wordTrace_append hprefix tailTrace_149669
  have hstable : (prefixWord ++ tailWord_149669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149669).length < 2 ^ (prefixWord ++ tailWord_149669).sum := by decide
  have hdescent : baseEnd_149669 < baseStart_149669 := by decide
  rcases family_descends (prefixWord ++ tailWord_149669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149718 : List Nat := [5, 2, 1, 2, 1, 1, 2, 8]
def baseStart_149718 : Nat := 118140960795 + 149718 * 2 ^ 59
def prefixEnd_149718 : Nat := 4983230072969 + 3 ^ 40 * 149718 * 2
def baseEnd_149718 : Nat := 5694614565181515654553

theorem tailTrace_149718 : CollatzResearch.WordTrace tailWord_149718 prefixEnd_149718 5694614565181515654553 := by
  unfold tailWord_149718
  simp only [CollatzResearch.WordTrace]
  refine ⟨341291504475295665237113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3640442714403153762529205 341291504475295665237113)
  ·
    refine ⟨255968628356471748927835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 341291504475295665237113 255968628356471748927835)
    ·
      refine ⟨383952942534707623391753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255968628356471748927835 383952942534707623391753)
      ·
        refine ⟨287964706901030717543815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383952942534707623391753 287964706901030717543815)
        ·
          refine ⟨431947060351546076315723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287964706901030717543815 431947060351546076315723)
          ·
            refine ⟨647920590527319114473585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431947060351546076315723 647920590527319114473585)
            ·
              refine ⟨485940442895489335855189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647920590527319114473585 485940442895489335855189)
              ·
                refine ⟨5694614565181515654553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 485940442895489335855189 5694614565181515654553)
                ·
                  rfl

theorem cell22_149718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_149718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149718 prefixEnd_149718 := by exact prefixLift 149718
  have htrace : WordTrace (prefixWord ++ tailWord_149718) baseStart_149718 baseEnd_149718 := by
    simpa [prefixWord, tailWord_149718, baseEnd_149718] using wordTrace_append hprefix tailTrace_149718
  have hstable : (prefixWord ++ tailWord_149718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149718).length < 2 ^ (prefixWord ++ tailWord_149718).sum := by decide
  have hdescent : baseEnd_149718 < baseStart_149718 := by decide
  rcases family_descends (prefixWord ++ tailWord_149718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149744 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_149744 : Nat := 118140960795 + 149744 * 2 ^ 59
def prefixEnd_149744 : Nat := 4983230072969 + 3 ^ 40 * 149744 * 2
def baseEnd_149744 : Nat := 51260431417978239740897

theorem tailTrace_149744 : CollatzResearch.WordTrace tailWord_149744 prefixEnd_149744 51260431417978239740897 := by
  unfold tailWord_149744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730806184755268542120143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3641074913007024722826857 2730806184755268542120143)
  ·
    refine ⟨4096209277132902813180215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2730806184755268542120143 4096209277132902813180215)
    ·
      refine ⟨6144313915699354219770323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096209277132902813180215 6144313915699354219770323)
      ·
        refine ⟨9216470873549031329655485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6144313915699354219770323 9216470873549031329655485)
        ·
          refine ⟨3456176577580886748620807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9216470873549031329655485 3456176577580886748620807)
          ·
            refine ⟨5184264866371330122931211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3456176577580886748620807 5184264866371330122931211)
            ·
              refine ⟨7776397299556995184396817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184264866371330122931211 7776397299556995184396817)
              ·
                refine ⟨5832297974667746388297613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7776397299556995184396817 5832297974667746388297613)
                ·
                  refine ⟨2187111740500404895611605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5832297974667746388297613 2187111740500404895611605)
                  ·
                    refine ⟨51260431417978239740897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2187111740500404895611605 51260431417978239740897)
                    ·
                      rfl

theorem cell22_149744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_149744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149744 prefixEnd_149744 := by exact prefixLift 149744
  have htrace : WordTrace (prefixWord ++ tailWord_149744) baseStart_149744 baseEnd_149744 := by
    simpa [prefixWord, tailWord_149744, baseEnd_149744] using wordTrace_append hprefix tailTrace_149744
  have hstable : (prefixWord ++ tailWord_149744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149744).length < 2 ^ (prefixWord ++ tailWord_149744).sum := by decide
  have hdescent : baseEnd_149744 < baseStart_149744 := by decide
  rcases family_descends (prefixWord ++ tailWord_149744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149761 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_149761 : Nat := 118140960795 + 149761 * 2 ^ 59
def prefixEnd_149761 : Nat := 4983230072969 + 3 ^ 40 * 149761 * 2
def baseEnd_149761 : Nat := 51266250865395862065845

theorem tailTrace_149761 : CollatzResearch.WordTrace tailWord_149761 prefixEnd_149761 51266250865395862065845 := by
  unfold tailWord_149761
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462232410448948987609137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3641488273632632658406091 5462232410448948987609137)
  ·
    refine ⟨4096674307836711740706853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5462232410448948987609137 4096674307836711740706853)
    ·
      refine ⟨768126432719383451382535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4096674307836711740706853 768126432719383451382535)
      ·
        refine ⟨1152189649079075177073803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768126432719383451382535 1152189649079075177073803)
        ·
          refine ⟨1728284473618612765610705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152189649079075177073803 1728284473618612765610705)
          ·
            refine ⟨1296213355213959574208029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728284473618612765610705 1296213355213959574208029)
            ·
              refine ⟨486080008205234840328011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1296213355213959574208029 486080008205234840328011)
              ·
                refine ⟨729120012307852260492017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486080008205234840328011 729120012307852260492017)
                ·
                  refine ⟨546840009230889195369013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 729120012307852260492017 546840009230889195369013)
                  ·
                    refine ⟨51266250865395862065845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 546840009230889195369013 51266250865395862065845)
                    ·
                      rfl

theorem cell22_149761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_149761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149761 prefixEnd_149761 := by exact prefixLift 149761
  have htrace : WordTrace (prefixWord ++ tailWord_149761) baseStart_149761 baseEnd_149761 := by
    simpa [prefixWord, tailWord_149761, baseEnd_149761] using wordTrace_append hprefix tailTrace_149761
  have hstable : (prefixWord ++ tailWord_149761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149761).length < 2 ^ (prefixWord ++ tailWord_149761).sum := by decide
  have hdescent : baseEnd_149761 < baseStart_149761 := by decide
  rcases family_descends (prefixWord ++ tailWord_149761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149836 : List Nat := [2, 2, 1, 3, 2, 1, 3, 8]
def baseStart_149836 : Nat := 118140960795 + 149836 * 2 ^ 59
def prefixEnd_149836 : Nat := 4983230072969 + 3 ^ 40 * 149836 * 2
def baseEnd_149836 : Nat := 5699102766457851826735

theorem tailTrace_149836 : CollatzResearch.WordTrace tailWord_149836 prefixEnd_149836 5699102766457851826735 := by
  unfold tailWord_149836
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732483942588618398294681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3643311923451491197726241 2732483942588618398294681)
  ·
    refine ⟨2049362956941463798721011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2732483942588618398294681 2049362956941463798721011)
    ·
      refine ⟨3074044435412195698081517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2049362956941463798721011 3074044435412195698081517)
      ·
        refine ⟨1152766663279573386780569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3074044435412195698081517 1152766663279573386780569)
        ·
          refine ⟨864574997459680040085427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152766663279573386780569 864574997459680040085427)
          ·
            refine ⟨1296862496189520060128141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864574997459680040085427 1296862496189520060128141)
            ·
              refine ⟨486323436071070022548053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1296862496189520060128141 486323436071070022548053)
              ·
                refine ⟨5699102766457851826735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 486323436071070022548053 5699102766457851826735)
                ·
                  rfl

theorem cell22_149836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 8].length) (baseStart_149836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149836 prefixEnd_149836 := by exact prefixLift 149836
  have htrace : WordTrace (prefixWord ++ tailWord_149836) baseStart_149836 baseEnd_149836 := by
    simpa [prefixWord, tailWord_149836, baseEnd_149836] using wordTrace_append hprefix tailTrace_149836
  have hstable : (prefixWord ++ tailWord_149836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149836).length < 2 ^ (prefixWord ++ tailWord_149836).sum := by decide
  have hdescent : baseEnd_149836 < baseStart_149836 := by decide
  rcases family_descends (prefixWord ++ tailWord_149836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149910 : List Nat := [5, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_149910 : Nat := 118140960795 + 149910 * 2 ^ 59
def prefixEnd_149910 : Nat := 4983230072969 + 3 ^ 40 * 149910 * 2
def baseEnd_149910 : Nat := 17105752203469713363463

theorem tailTrace_149910 : CollatzResearch.WordTrace tailWord_149910 prefixEnd_149910 17105752203469713363463 := by
  unfold tailWord_149910
  simp only [CollatzResearch.WordTrace]
  refine ⟨341729180431821714673949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3645111257939431623188789 341729180431821714673949)
  ·
    refine ⟨128148442661933143002731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 341729180431821714673949 128148442661933143002731)
    ·
      refine ⟨192222663992899714504097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128148442661933143002731 192222663992899714504097)
      ·
        refine ⟨144166997994674785878073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192222663992899714504097 144166997994674785878073)
        ·
          refine ⟨108125248496006089408555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144166997994674785878073 108125248496006089408555)
          ·
            refine ⟨162187872744009134112833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108125248496006089408555 162187872744009134112833)
            ·
              refine ⟨121640904558006850584625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162187872744009134112833 121640904558006850584625)
              ·
                refine ⟨91230678418505137938469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121640904558006850584625 91230678418505137938469)
                ·
                  refine ⟨17105752203469713363463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91230678418505137938469 17105752203469713363463)
                  ·
                    rfl

theorem cell22_149910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_149910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149910 prefixEnd_149910 := by exact prefixLift 149910
  have htrace : WordTrace (prefixWord ++ tailWord_149910) baseStart_149910 baseEnd_149910 := by
    simpa [prefixWord, tailWord_149910, baseEnd_149910] using wordTrace_append hprefix tailTrace_149910
  have hstable : (prefixWord ++ tailWord_149910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149910).length < 2 ^ (prefixWord ++ tailWord_149910).sum := by decide
  have hdescent : baseEnd_149910 < baseStart_149910 := by decide
  rcases family_descends (prefixWord ++ tailWord_149910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149943 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 6]
def baseStart_149943 : Nat := 118140960795 + 149943 * 2 ^ 59
def prefixEnd_149943 : Nat := 4983230072969 + 3 ^ 40 * 149943 * 2
def baseEnd_149943 : Nat := 17109517728269351338429

theorem tailTrace_149943 : CollatzResearch.WordTrace tailWord_149943 prefixEnd_149943 17109517728269351338429 := by
  unfold tailWord_149943
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468870495789594070734483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3645913663859729380489655 5468870495789594070734483)
  ·
    refine ⟨8203305743684391106101725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5468870495789594070734483 8203305743684391106101725)
    ·
      refine ⟨3076239653881646664788147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8203305743684391106101725 3076239653881646664788147)
      ·
        refine ⟨4614359480822469997182221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076239653881646664788147 4614359480822469997182221)
        ·
          refine ⟨1730384805308426248943333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4614359480822469997182221 1730384805308426248943333)
          ·
            refine ⟨324447150995329921676875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1730384805308426248943333 324447150995329921676875)
            ·
              refine ⟨486670726492994882515313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324447150995329921676875 486670726492994882515313)
              ·
                refine ⟨365003044869746161886485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486670726492994882515313 365003044869746161886485)
                ·
                  refine ⟨17109517728269351338429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 365003044869746161886485 17109517728269351338429)
                  ·
                    rfl

theorem cell22_149943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 6].length) (baseStart_149943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149943 prefixEnd_149943 := by exact prefixLift 149943
  have htrace : WordTrace (prefixWord ++ tailWord_149943) baseStart_149943 baseEnd_149943 := by
    simpa [prefixWord, tailWord_149943, baseEnd_149943] using wordTrace_append hprefix tailTrace_149943
  have hstable : (prefixWord ++ tailWord_149943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149943).length < 2 ^ (prefixWord ++ tailWord_149943).sum := by decide
  have hdescent : baseEnd_149943 < baseStart_149943 := by decide
  rcases family_descends (prefixWord ++ tailWord_149943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149953 : List Nat := [1, 2, 7, 1, 1, 1, 2, 3, 1, 3]
def baseStart_149953 : Nat := 118140960795 + 149953 * 2 ^ 59
def prefixEnd_149953 : Nat := 4983230072969 + 3 ^ 40 * 149953 * 2
def baseEnd_149953 : Nat := 51331976389171361265257

theorem tailTrace_149953 : CollatzResearch.WordTrace tailWord_149953 prefixEnd_149953 51331976389171361265257 := by
  unfold tailWord_149953
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469235225753365778598513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3646156817168910519065675 5469235225753365778598513)
  ·
    refine ⟨4101926419315024333948885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5469235225753365778598513 4101926419315024333948885)
    ·
      refine ⟨96138900452695882826927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4101926419315024333948885 96138900452695882826927)
      ·
        refine ⟨144208350679043824240391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96138900452695882826927 144208350679043824240391)
        ·
          refine ⟨216312526018565736360587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144208350679043824240391 216312526018565736360587)
          ·
            refine ⟨324468789027848604540881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216312526018565736360587 324468789027848604540881)
            ·
              refine ⟨243351591770886453405661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324468789027848604540881 243351591770886453405661)
              ·
                refine ⟨91256846914082420027123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243351591770886453405661 91256846914082420027123)
                ·
                  refine ⟨136885270371123630040685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91256846914082420027123 136885270371123630040685)
                  ·
                    refine ⟨51331976389171361265257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136885270371123630040685 51331976389171361265257)
                    ·
                      rfl

theorem cell22_149953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_149953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149953 prefixEnd_149953 := by exact prefixLift 149953
  have htrace : WordTrace (prefixWord ++ tailWord_149953) baseStart_149953 baseEnd_149953 := by
    simpa [prefixWord, tailWord_149953, baseEnd_149953] using wordTrace_append hprefix tailTrace_149953
  have hstable : (prefixWord ++ tailWord_149953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149953).length < 2 ^ (prefixWord ++ tailWord_149953).sum := by decide
  have hdescent : baseEnd_149953 < baseStart_149953 := by decide
  rcases family_descends (prefixWord ++ tailWord_149953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149960 : List Nat := [2, 1, 3, 1, 3, 2, 1, 5, 4]
def baseStart_149960 : Nat := 118140960795 + 149960 * 2 ^ 59
def prefixEnd_149960 : Nat := 4983230072969 + 3 ^ 40 * 149960 * 2
def baseEnd_149960 : Nat := 17111457544075225446745

theorem tailTrace_149960 : CollatzResearch.WordTrace tailWord_149960 prefixEnd_149960 17111457544075225446745 := by
  unfold tailWord_149960
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734745268364002987051667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3646327024485337316068889 2734745268364002987051667)
  ·
    refine ⟨4102117902546004480577501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2734745268364002987051667 4102117902546004480577501)
    ·
      refine ⟨1538294213454751680216563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4102117902546004480577501 1538294213454751680216563)
      ·
        refine ⟨2307441320182127520324845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1538294213454751680216563 2307441320182127520324845)
        ·
          refine ⟨865290495068297820121817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2307441320182127520324845 865290495068297820121817)
          ·
            refine ⟨648967871301223365091363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865290495068297820121817 648967871301223365091363)
            ·
              refine ⟨973451806951835047637045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648967871301223365091363 973451806951835047637045)
              ·
                refine ⟨91261106901734535715973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973451806951835047637045 91261106901734535715973)
                ·
                  refine ⟨17111457544075225446745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91261106901734535715973 17111457544075225446745)
                  ·
                    rfl

theorem cell22_149960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_149960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_149960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_149960 prefixEnd_149960 := by exact prefixLift 149960
  have htrace : WordTrace (prefixWord ++ tailWord_149960) baseStart_149960 baseEnd_149960 := by
    simpa [prefixWord, tailWord_149960, baseEnd_149960] using wordTrace_append hprefix tailTrace_149960
  have hstable : (prefixWord ++ tailWord_149960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149960).length < 2 ^ (prefixWord ++ tailWord_149960).sum := by decide
  have hdescent : baseEnd_149960 < baseStart_149960 := by decide
  rcases family_descends (prefixWord ++ tailWord_149960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150080 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_150080 : Nat := 118140960795 + 150080 * 2 ^ 59
def prefixEnd_150080 : Nat := 4983230072969 + 3 ^ 40 * 150080 * 2
def baseEnd_150080 : Nat := 51375451084585363339867

theorem tailTrace_150080 : CollatzResearch.WordTrace tailWord_150080 prefixEnd_150080 51375451084585363339867 := by
  unfold tailWord_150080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736933648146633234235847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3649244864195510978981129 2736933648146633234235847)
  ·
    refine ⟨4105400472219949851353771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2736933648146633234235847 4105400472219949851353771)
    ·
      refine ⟨6158100708329924777030657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4105400472219949851353771 6158100708329924777030657)
      ·
        refine ⟨4618575531247443582772993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6158100708329924777030657 4618575531247443582772993)
        ·
          refine ⟨3463931648435582687079745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4618575531247443582772993 3463931648435582687079745)
          ·
            refine ⟨2597948736326687015309809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3463931648435582687079745 2597948736326687015309809)
            ·
              refine ⟨1948461552245015261482357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2597948736326687015309809 1948461552245015261482357)
              ·
                refine ⟨182668270522970180763971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1948461552245015261482357 182668270522970180763971)
                ·
                  refine ⟨274002405784455271145957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182668270522970180763971 274002405784455271145957)
                  ·
                    refine ⟨51375451084585363339867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274002405784455271145957 51375451084585363339867)
                    ·
                      rfl

theorem cell22_150080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_150080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150080 prefixEnd_150080 := by exact prefixLift 150080
  have htrace : WordTrace (prefixWord ++ tailWord_150080) baseStart_150080 baseEnd_150080 := by
    simpa [prefixWord, tailWord_150080, baseEnd_150080] using wordTrace_append hprefix tailTrace_150080
  have hstable : (prefixWord ++ tailWord_150080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150080).length < 2 ^ (prefixWord ++ tailWord_150080).sum := by decide
  have hdescent : baseEnd_150080 < baseStart_150080 := by decide
  rcases family_descends (prefixWord ++ tailWord_150080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150144 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 2, 3]
def baseStart_150144 : Nat := 118140960795 + 150144 * 2 ^ 59
def prefixEnd_150144 : Nat := 4983230072969 + 3 ^ 40 * 150144 * 2
def baseEnd_150144 : Nat := 51397359592510529739671

theorem tailTrace_150144 : CollatzResearch.WordTrace tailWord_150144 prefixEnd_150144 51397359592510529739671 := by
  unfold tailWord_150144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2738100784030702699400743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3650801045374270265867657 2738100784030702699400743)
  ·
    refine ⟨4107151176046054049101115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2738100784030702699400743 4107151176046054049101115)
    ·
      refine ⟨6160726764069081073651673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107151176046054049101115 6160726764069081073651673)
      ·
        refine ⟨4620545073051810805238755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6160726764069081073651673 4620545073051810805238755)
        ·
          refine ⟨6930817609577716207858133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620545073051810805238755 6930817609577716207858133)
          ·
            refine ⟨162441037724477723621675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 6930817609577716207858133 162441037724477723621675)
            ·
              refine ⟨243661556586716585432513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162441037724477723621675 243661556586716585432513)
              ·
                refine ⟨182746167440037439074385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243661556586716585432513 182746167440037439074385)
                ·
                  refine ⟨137059625580028079305789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182746167440037439074385 137059625580028079305789)
                  ·
                    refine ⟨51397359592510529739671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137059625580028079305789 51397359592510529739671)
                    ·
                      rfl

theorem cell22_150144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_150144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150144 prefixEnd_150144 := by exact prefixLift 150144
  have htrace : WordTrace (prefixWord ++ tailWord_150144) baseStart_150144 baseEnd_150144 := by
    simpa [prefixWord, tailWord_150144, baseEnd_150144] using wordTrace_append hprefix tailTrace_150144
  have hstable : (prefixWord ++ tailWord_150144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150144).length < 2 ^ (prefixWord ++ tailWord_150144).sum := by decide
  have hdescent : baseEnd_150144 < baseStart_150144 := by decide
  rcases family_descends (prefixWord ++ tailWord_150144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150232 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_150232 : Nat := 118140960795 + 150232 * 2 ^ 59
def prefixEnd_150232 : Nat := 4983230072969 + 3 ^ 40 * 150232 * 2
def baseEnd_150232 : Nat := 51427483790907633539401

theorem tailTrace_150232 : CollatzResearch.WordTrace tailWord_150232 prefixEnd_150232 51427483790907633539401 := by
  unfold tailWord_150232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739705595871298214002475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3652940794495064285336633 2739705595871298214002475)
  ·
    refine ⟨4109558393806947321003713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739705595871298214002475 4109558393806947321003713)
    ·
      refine ⟨3082168795355210490752785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4109558393806947321003713 3082168795355210490752785)
      ·
        refine ⟨2311626596516407868064589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3082168795355210490752785 2311626596516407868064589)
        ·
          refine ⟨866859973693652950524221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2311626596516407868064589 866859973693652950524221)
          ·
            refine ⟨325072490135119856446583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 866859973693652950524221 325072490135119856446583)
            ·
              refine ⟨487608735202679784669875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325072490135119856446583 487608735202679784669875)
              ·
                refine ⟨731413102804019677004813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487608735202679784669875 731413102804019677004813)
                ·
                  refine ⟨274279913551507378876805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731413102804019677004813 274279913551507378876805)
                  ·
                    refine ⟨51427483790907633539401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274279913551507378876805 51427483790907633539401)
                    ·
                      rfl

theorem cell22_150232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_150232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150232 prefixEnd_150232 := by exact prefixLift 150232
  have htrace : WordTrace (prefixWord ++ tailWord_150232) baseStart_150232 baseEnd_150232 := by
    simpa [prefixWord, tailWord_150232, baseEnd_150232] using wordTrace_append hprefix tailTrace_150232
  have hstable : (prefixWord ++ tailWord_150232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150232).length < 2 ^ (prefixWord ++ tailWord_150232).sum := by decide
  have hdescent : baseEnd_150232 < baseStart_150232 := by decide
  rcases family_descends (prefixWord ++ tailWord_150232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150262 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_150262 : Nat := 118140960795 + 150262 * 2 ^ 59
def prefixEnd_150262 : Nat := 4983230072969 + 3 ^ 40 * 150262 * 2
def baseEnd_150262 : Nat := 51437753403997555289309

theorem tailTrace_150262 : CollatzResearch.WordTrace tailWord_150262 prefixEnd_150262 51437753403997555289309 := by
  unfold tailWord_150262
  simp only [CollatzResearch.WordTrace]
  refine ⟨342531586352119471974815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3653670254422607701064693 342531586352119471974815)
  ·
    refine ⟨513797379528179207962223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342531586352119471974815 513797379528179207962223)
    ·
      refine ⟨770696069292268811943335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513797379528179207962223 770696069292268811943335)
      ·
        refine ⟨1156044103938403217915003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770696069292268811943335 1156044103938403217915003)
        ·
          refine ⟨1734066155907604826872505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156044103938403217915003 1734066155907604826872505)
          ·
            refine ⟨1300549616930703620154379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734066155907604826872505 1300549616930703620154379)
            ·
              refine ⟨1950824425396055430231569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300549616930703620154379 1950824425396055430231569)
              ·
                refine ⟨1463118319047041572673677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950824425396055430231569 1463118319047041572673677)
                ·
                  refine ⟨548669369642640589752629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1463118319047041572673677 548669369642640589752629)
                  ·
                    refine ⟨51437753403997555289309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 548669369642640589752629 51437753403997555289309)
                    ·
                      rfl

theorem cell22_150262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_150262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150262 prefixEnd_150262 := by exact prefixLift 150262
  have htrace : WordTrace (prefixWord ++ tailWord_150262) baseStart_150262 baseEnd_150262 := by
    simpa [prefixWord, tailWord_150262, baseEnd_150262] using wordTrace_append hprefix tailTrace_150262
  have hstable : (prefixWord ++ tailWord_150262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150262).length < 2 ^ (prefixWord ++ tailWord_150262).sum := by decide
  have hdescent : baseEnd_150262 < baseStart_150262 := by decide
  rcases family_descends (prefixWord ++ tailWord_150262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150279 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 1, 5]
def baseStart_150279 : Nat := 118140960795 + 150279 * 2 ^ 59
def prefixEnd_150279 : Nat := 4983230072969 + 3 ^ 40 * 150279 * 2
def baseEnd_150279 : Nat := 51443572851415177614257

theorem tailTrace_150279 : CollatzResearch.WordTrace tailWord_150279 prefixEnd_150279 51443572851415177614257 := by
  unfold tailWord_150279
  simp only [CollatzResearch.WordTrace]
  refine ⟨5481125422572323454965891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3654083615048215636643927 5481125422572323454965891)
  ·
    refine ⟨8221688133858485182448837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5481125422572323454965891 8221688133858485182448837)
    ·
      refine ⟨1541566525098465971709157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8221688133858485182448837 1541566525098465971709157)
      ·
        refine ⟨289043723455962369695467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1541566525098465971709157 289043723455962369695467)
        ·
          refine ⟨433565585183943554543201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289043723455962369695467 433565585183943554543201)
          ·
            refine ⟨325174188887957665907401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433565585183943554543201 325174188887957665907401)
            ·
              refine ⟨243880641665968249430551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325174188887957665907401 243880641665968249430551)
              ·
                refine ⟨365820962498952374145827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243880641665968249430551 365820962498952374145827)
                ·
                  refine ⟨548731443748428561218741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365820962498952374145827 548731443748428561218741)
                  ·
                    refine ⟨51443572851415177614257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 548731443748428561218741 51443572851415177614257)
                    ·
                      rfl

theorem cell22_150279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_150279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150279 prefixEnd_150279 := by exact prefixLift 150279
  have htrace : WordTrace (prefixWord ++ tailWord_150279) baseStart_150279 baseEnd_150279 := by
    simpa [prefixWord, tailWord_150279, baseEnd_150279] using wordTrace_append hprefix tailTrace_150279
  have hstable : (prefixWord ++ tailWord_150279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150279).length < 2 ^ (prefixWord ++ tailWord_150279).sum := by decide
  have hdescent : baseEnd_150279 < baseStart_150279 := by decide
  rcases family_descends (prefixWord ++ tailWord_150279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150307 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 7, 3]
def baseStart_150307 : Nat := 118140960795 + 150307 * 2 ^ 59
def prefixEnd_150307 : Nat := 4983230072969 + 3 ^ 40 * 150307 * 2
def baseEnd_150307 : Nat := 51453157823632437914171

theorem tailTrace_150307 : CollatzResearch.WordTrace tailWord_150307 prefixEnd_150307 51453157823632437914171 := by
  unfold tailWord_150307
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482146666470884236985175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3654764444313922824656783 5482146666470884236985175)
  ·
    refine ⟨8223219999706326355477763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5482146666470884236985175 8223219999706326355477763)
    ·
      refine ⟨12334829999559489533216645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8223219999706326355477763 12334829999559489533216645)
      ·
        refine ⟨2312780624917404287478121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12334829999559489533216645 2312780624917404287478121)
        ·
          refine ⟨1734585468688053215608591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312780624917404287478121 1734585468688053215608591)
          ·
            refine ⟨2601878203032079823412887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734585468688053215608591 2601878203032079823412887)
            ·
              refine ⟨3902817304548119735119331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601878203032079823412887 3902817304548119735119331)
              ·
                refine ⟨5854225956822179602678997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902817304548119735119331 5854225956822179602678997)
                ·
                  refine ⟨137208420863019834437789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5854225956822179602678997 137208420863019834437789)
                  ·
                    refine ⟨51453157823632437914171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137208420863019834437789 51453157823632437914171)
                    ·
                      rfl

theorem cell22_150307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 3].length) (baseStart_150307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150307 prefixEnd_150307 := by exact prefixLift 150307
  have htrace : WordTrace (prefixWord ++ tailWord_150307) baseStart_150307 baseEnd_150307 := by
    simpa [prefixWord, tailWord_150307, baseEnd_150307] using wordTrace_append hprefix tailTrace_150307
  have hstable : (prefixWord ++ tailWord_150307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150307).length < 2 ^ (prefixWord ++ tailWord_150307).sum := by decide
  have hdescent : baseEnd_150307 < baseStart_150307 := by decide
  rcases family_descends (prefixWord ++ tailWord_150307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150412 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_150412 : Nat := 118140960795 + 150412 * 2 ^ 59
def prefixEnd_150412 : Nat := 4983230072969 + 3 ^ 40 * 150412 * 2
def baseEnd_150412 : Nat := 51489101469447164038849

theorem tailTrace_150412 : CollatzResearch.WordTrace tailWord_150412 prefixEnd_150412 51489101469447164038849 := by
  unfold tailWord_150412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742988165545243584778745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3657317554060324779704993 2742988165545243584778745)
  ·
    refine ⟨2057241124158932688584059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2742988165545243584778745 2057241124158932688584059)
    ·
      refine ⟨3085861686238399032876089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2057241124158932688584059 3085861686238399032876089)
      ·
        refine ⟨2314396264678799274657067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3085861686238399032876089 2314396264678799274657067)
        ·
          refine ⟨3471594397018198911985601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314396264678799274657067 3471594397018198911985601)
          ·
            refine ⟨2603695797763649183989201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3471594397018198911985601 2603695797763649183989201)
            ·
              refine ⟨1952771848322736887991901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2603695797763649183989201 1952771848322736887991901)
              ·
                refine ⟨732289443121026332996963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1952771848322736887991901 732289443121026332996963)
                ·
                  refine ⟨1098434164681539499495445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732289443121026332996963 1098434164681539499495445)
                  ·
                    refine ⟨51489101469447164038849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1098434164681539499495445 51489101469447164038849)
                    ·
                      rfl

theorem cell22_150412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_150412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150412 prefixEnd_150412 := by exact prefixLift 150412
  have htrace : WordTrace (prefixWord ++ tailWord_150412) baseStart_150412 baseEnd_150412 := by
    simpa [prefixWord, tailWord_150412, baseEnd_150412] using wordTrace_append hprefix tailTrace_150412
  have hstable : (prefixWord ++ tailWord_150412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150412).length < 2 ^ (prefixWord ++ tailWord_150412).sum := by decide
  have hdescent : baseEnd_150412 < baseStart_150412 := by decide
  rcases family_descends (prefixWord ++ tailWord_150412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150429 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_150429 : Nat := 118140960795 + 150429 * 2 ^ 59
def prefixEnd_150429 : Nat := 4983230072969 + 3 ^ 40 * 150429 * 2
def baseEnd_150429 : Nat := 51494920916864786363797

theorem tailTrace_150429 : CollatzResearch.WordTrace tailWord_150429 prefixEnd_150429 51494920916864786363797 := by
  unfold tailWord_150429
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486596372028899072926341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3657730914685932715284227 5486596372028899072926341)
  ·
    refine ⟨1028736819755418576173689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5486596372028899072926341 1028736819755418576173689)
    ·
      refine ⟨771552614816563932130267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1028736819755418576173689 771552614816563932130267)
      ·
        refine ⟨1157328922224845898195401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771552614816563932130267 1157328922224845898195401)
        ·
          refine ⟨867996691668634423646551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1157328922224845898195401 867996691668634423646551)
          ·
            refine ⟨1301995037502951635469827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867996691668634423646551 1301995037502951635469827)
            ·
              refine ⟨1952992556254427453204741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301995037502951635469827 1952992556254427453204741)
              ·
                refine ⟨366186104297705147475889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1952992556254427453204741 366186104297705147475889)
                ·
                  refine ⟨274639578223278860606917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366186104297705147475889 274639578223278860606917)
                  ·
                    refine ⟨51494920916864786363797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274639578223278860606917 51494920916864786363797)
                    ·
                      rfl

theorem cell22_150429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_150429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150429 prefixEnd_150429 := by exact prefixLift 150429
  have htrace : WordTrace (prefixWord ++ tailWord_150429) baseStart_150429 baseEnd_150429 := by
    simpa [prefixWord, tailWord_150429, baseEnd_150429] using wordTrace_append hprefix tailTrace_150429
  have hstable : (prefixWord ++ tailWord_150429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150429).length < 2 ^ (prefixWord ++ tailWord_150429).sum := by decide
  have hdescent : baseEnd_150429 < baseStart_150429 := by decide
  rcases family_descends (prefixWord ++ tailWord_150429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150431 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 2, 3]
def baseStart_150431 : Nat := 118140960795 + 150431 * 2 ^ 59
def prefixEnd_150431 : Nat := 4983230072969 + 3 ^ 40 * 150431 * 2
def baseEnd_150431 : Nat := 51495605557737447813791

theorem tailTrace_150431 : CollatzResearch.WordTrace tailWord_150431 prefixEnd_150431 51495605557737447813791 := by
  unfold tailWord_150431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486669318021653414499147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3657779545347768942999431 5486669318021653414499147)
  ·
    refine ⟨8230003977032480121748721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5486669318021653414499147 8230003977032480121748721)
    ·
      refine ⟨6172502982774360091311541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8230003977032480121748721 6172502982774360091311541)
      ·
        refine ⟨578672154635096258560457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6172502982774360091311541 578672154635096258560457)
        ·
          refine ⟨434004115976322193920343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578672154635096258560457 434004115976322193920343)
          ·
            refine ⟨651006173964483290880515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434004115976322193920343 651006173964483290880515)
            ·
              refine ⟨976509260946724936320773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651006173964483290880515 976509260946724936320773)
              ·
                refine ⟨183095486427510925560145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 976509260946724936320773 183095486427510925560145)
                ·
                  refine ⟨137321614820633194170109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183095486427510925560145 137321614820633194170109)
                  ·
                    refine ⟨51495605557737447813791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137321614820633194170109 51495605557737447813791)
                    ·
                      rfl

theorem cell22_150431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_150431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150431 prefixEnd_150431 := by exact prefixLift 150431
  have htrace : WordTrace (prefixWord ++ tailWord_150431) baseStart_150431 baseEnd_150431 := by
    simpa [prefixWord, tailWord_150431, baseEnd_150431] using wordTrace_append hprefix tailTrace_150431
  have hstable : (prefixWord ++ tailWord_150431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150431).length < 2 ^ (prefixWord ++ tailWord_150431).sum := by decide
  have hdescent : baseEnd_150431 < baseStart_150431 := by decide
  rcases family_descends (prefixWord ++ tailWord_150431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150433 : List Nat := [1, 2, 3, 4, 1, 1, 4, 2, 4]
def baseStart_150433 : Nat := 118140960795 + 150433 * 2 ^ 59
def prefixEnd_150433 : Nat := 4983230072969 + 3 ^ 40 * 150433 * 2
def baseEnd_150433 : Nat := 17165430066203369754595

theorem tailTrace_150433 : CollatzResearch.WordTrace tailWord_150433 prefixEnd_150433 17165430066203369754595 := by
  unfold tailWord_150433
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486742264014407756071953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3657828176009605170714635 5486742264014407756071953)
  ·
    refine ⟨4115056698010805817053965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5486742264014407756071953 4115056698010805817053965)
    ·
      refine ⟨1543146261754052181395237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4115056698010805817053965 1543146261754052181395237)
      ·
        refine ⟨289339924078884784011607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1543146261754052181395237 289339924078884784011607)
        ·
          refine ⟨434009886118327176017411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289339924078884784011607 434009886118327176017411)
          ·
            refine ⟨651014829177490764026117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434009886118327176017411 651014829177490764026117)
            ·
              refine ⟨122065280470779518254897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 651014829177490764026117 122065280470779518254897)
              ·
                refine ⟨91548960353084638691173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122065280470779518254897 91548960353084638691173)
                ·
                  refine ⟨17165430066203369754595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91548960353084638691173 17165430066203369754595)
                  ·
                    rfl

theorem cell22_150433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_150433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150433 prefixEnd_150433 := by exact prefixLift 150433
  have htrace : WordTrace (prefixWord ++ tailWord_150433) baseStart_150433 baseEnd_150433 := by
    simpa [prefixWord, tailWord_150433, baseEnd_150433] using wordTrace_append hprefix tailTrace_150433
  have hstable : (prefixWord ++ tailWord_150433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150433).length < 2 ^ (prefixWord ++ tailWord_150433).sum := by decide
  have hdescent : baseEnd_150433 < baseStart_150433 := by decide
  rcases family_descends (prefixWord ++ tailWord_150433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150461 : List Nat := [1, 4, 1, 2, 4, 1, 3, 6]
def baseStart_150461 : Nat := 118140960795 + 150461 * 2 ^ 59
def prefixEnd_150461 : Nat := 4983230072969 + 3 ^ 40 * 150461 * 2
def baseEnd_150461 : Nat := 5722875018980818840411

theorem tailTrace_150461 : CollatzResearch.WordTrace tailWord_150461 prefixEnd_150461 5722875018980818840411 := by
  unfold tailWord_150461
  simp only [CollatzResearch.WordTrace]
  refine ⟨5487763507912968538091237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3658509005275312358727491 5487763507912968538091237)
  ·
    refine ⟨1028955657733681600892107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5487763507912968538091237 1028955657733681600892107)
    ·
      refine ⟨1543433486600522401338161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028955657733681600892107 1543433486600522401338161)
      ·
        refine ⟨1157575114950391801003621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1543433486600522401338161 1157575114950391801003621)
        ·
          refine ⟨217045334053198462688179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1157575114950391801003621 217045334053198462688179)
          ·
            refine ⟨325568001079797694032269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217045334053198462688179 325568001079797694032269)
            ·
              refine ⟨122088000404924135262101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325568001079797694032269 122088000404924135262101)
              ·
                refine ⟨5722875018980818840411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122088000404924135262101 5722875018980818840411)
                ·
                  rfl

theorem cell22_150461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 6].length) (baseStart_150461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150461 prefixEnd_150461 := by exact prefixLift 150461
  have htrace : WordTrace (prefixWord ++ tailWord_150461) baseStart_150461 baseEnd_150461 := by
    simpa [prefixWord, tailWord_150461, baseEnd_150461] using wordTrace_append hprefix tailTrace_150461
  have hstable : (prefixWord ++ tailWord_150461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150461).length < 2 ^ (prefixWord ++ tailWord_150461).sum := by decide
  have hdescent : baseEnd_150461 < baseStart_150461 := by decide
  rcases family_descends (prefixWord ++ tailWord_150461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150489 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 7]
def baseStart_150489 : Nat := 118140960795 + 150489 * 2 ^ 59
def prefixEnd_150489 : Nat := 4983230072969 + 3 ^ 40 * 150489 * 2
def baseEnd_150489 : Nat := 17171820047681543287871

theorem tailTrace_150489 : CollatzResearch.WordTrace tailWord_150489 prefixEnd_150489 17171820047681543287871 := by
  unfold tailWord_150489
  simp only [CollatzResearch.WordTrace]
  refine ⟨5488784751811529320110521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3659189834541019546740347 5488784751811529320110521)
  ·
    refine ⟨4116588563858646990082891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5488784751811529320110521 4116588563858646990082891)
    ·
      refine ⟨6174882845787970485124337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4116588563858646990082891 6174882845787970485124337)
      ·
        refine ⟨4631162134340977863843253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6174882845787970485124337 4631162134340977863843253)
        ·
          refine ⟨434171450094466674735305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4631162134340977863843253 434171450094466674735305)
          ·
            refine ⟨325628587570850006051479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434171450094466674735305 325628587570850006051479)
            ·
              refine ⟨488442881356275009077219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325628587570850006051479 488442881356275009077219)
              ·
                refine ⟨732664322034412513615829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488442881356275009077219 732664322034412513615829)
                ·
                  refine ⟨17171820047681543287871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 732664322034412513615829 17171820047681543287871)
                  ·
                    rfl

theorem cell22_150489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_150489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150489 prefixEnd_150489 := by exact prefixLift 150489
  have htrace : WordTrace (prefixWord ++ tailWord_150489) baseStart_150489 baseEnd_150489 := by
    simpa [prefixWord, tailWord_150489, baseEnd_150489] using wordTrace_append hprefix tailTrace_150489
  have hstable : (prefixWord ++ tailWord_150489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150489).length < 2 ^ (prefixWord ++ tailWord_150489).sum := by decide
  have hdescent : baseEnd_150489 < baseStart_150489 := by decide
  rcases family_descends (prefixWord ++ tailWord_150489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150493 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_150493 : Nat := 118140960795 + 150493 * 2 ^ 59
def prefixEnd_150493 : Nat := 4983230072969 + 3 ^ 40 * 150493 * 2
def baseEnd_150493 : Nat := 51516829424789952763601

theorem tailTrace_150493 : CollatzResearch.WordTrace tailWord_150493 prefixEnd_150493 51516829424789952763601 := by
  unfold tailWord_150493
  simp only [CollatzResearch.WordTrace]
  refine ⟨5488930643797038003256133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3659287095864692002170755 5488930643797038003256133)
  ·
    refine ⟨1029174495711944625610525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5488930643797038003256133 1029174495711944625610525)
    ·
      refine ⟨385940435891979234603947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1029174495711944625610525 385940435891979234603947)
      ·
        refine ⟨578910653837968851905921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385940435891979234603947 578910653837968851905921)
        ·
          refine ⟨434182990378476638929441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578910653837968851905921 434182990378476638929441)
          ·
            refine ⟨325637242783857479197081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434182990378476638929441 325637242783857479197081)
            ·
              refine ⟨244227932087893109397811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325637242783857479197081 244227932087893109397811)
              ·
                refine ⟨366341898131839664096717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244227932087893109397811 366341898131839664096717)
                ·
                  refine ⟨137378211799439874036269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366341898131839664096717 137378211799439874036269)
                  ·
                    refine ⟨51516829424789952763601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137378211799439874036269 51516829424789952763601)
                    ·
                      rfl

theorem cell22_150493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_150493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150493 prefixEnd_150493 := by exact prefixLift 150493
  have htrace : WordTrace (prefixWord ++ tailWord_150493) baseStart_150493 baseEnd_150493 := by
    simpa [prefixWord, tailWord_150493, baseEnd_150493] using wordTrace_append hprefix tailTrace_150493
  have hstable : (prefixWord ++ tailWord_150493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150493).length < 2 ^ (prefixWord ++ tailWord_150493).sum := by decide
  have hdescent : baseEnd_150493 < baseStart_150493 := by decide
  rcases family_descends (prefixWord ++ tailWord_150493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150504 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_150504 : Nat := 118140960795 + 150504 * 2 ^ 59
def prefixEnd_150504 : Nat := 4983230072969 + 3 ^ 40 * 150504 * 2
def baseEnd_150504 : Nat := 51520594949589590738567

theorem tailTrace_150504 : CollatzResearch.WordTrace tailWord_150504 prefixEnd_150504 51520594949589590738567 := by
  unfold tailWord_150504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744665923378593440953283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3659554564504791254604377 2744665923378593440953283)
  ·
    refine ⟨4116998885067890161429925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2744665923378593440953283 4116998885067890161429925)
    ·
      refine ⟨771937290950229405268111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4116998885067890161429925 771937290950229405268111)
      ·
        refine ⟨1157905936425344107902167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771937290950229405268111 1157905936425344107902167)
        ·
          refine ⟨1736858904638016161853251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157905936425344107902167 1736858904638016161853251)
          ·
            refine ⟨2605288356957024242779877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736858904638016161853251 2605288356957024242779877)
            ·
              refine ⟨488491566929442045521227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2605288356957024242779877 488491566929442045521227)
              ·
                refine ⟨732737350394163068281841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488491566929442045521227 732737350394163068281841)
                ·
                  refine ⟨549553012795622301211381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 732737350394163068281841 549553012795622301211381)
                  ·
                    refine ⟨51520594949589590738567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 549553012795622301211381 51520594949589590738567)
                    ·
                      rfl

theorem cell22_150504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_150504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150504 prefixEnd_150504 := by exact prefixLift 150504
  have htrace : WordTrace (prefixWord ++ tailWord_150504) baseStart_150504 baseEnd_150504 := by
    simpa [prefixWord, tailWord_150504, baseEnd_150504] using wordTrace_append hprefix tailTrace_150504
  have hstable : (prefixWord ++ tailWord_150504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150504).length < 2 ^ (prefixWord ++ tailWord_150504).sum := by decide
  have hdescent : baseEnd_150504 < baseStart_150504 := by decide
  rcases family_descends (prefixWord ++ tailWord_150504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150536 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_150536 : Nat := 118140960795 + 150536 * 2 ^ 59
def prefixEnd_150536 : Nat := 4983230072969 + 3 ^ 40 * 150536 * 2
def baseEnd_150536 : Nat := 51531549203552173938469

theorem tailTrace_150536 : CollatzResearch.WordTrace tailWord_150536 prefixEnd_150536 51531549203552173938469 := by
  unfold tailWord_150536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745249491320628173535731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3660332655094170898047641 2745249491320628173535731)
  ·
    refine ⟨4117874236980942260303597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2745249491320628173535731 4117874236980942260303597)
    ·
      refine ⟨1544202838867853347613849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4117874236980942260303597 1544202838867853347613849)
      ·
        refine ⟨1158152129150890010710387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544202838867853347613849 1158152129150890010710387)
        ·
          refine ⟨1737228193726335016065581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158152129150890010710387 1737228193726335016065581)
          ·
            refine ⟨651460572647375631024593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1737228193726335016065581 651460572647375631024593)
            ·
              refine ⟨488595429485531723268445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651460572647375631024593 488595429485531723268445)
              ·
                refine ⟨183223286057074396225667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488595429485531723268445 183223286057074396225667)
                ·
                  refine ⟨274834929085611594338501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183223286057074396225667 274834929085611594338501)
                  ·
                    refine ⟨51531549203552173938469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274834929085611594338501 51531549203552173938469)
                    ·
                      rfl

theorem cell22_150536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_150536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150536 prefixEnd_150536 := by exact prefixLift 150536
  have htrace : WordTrace (prefixWord ++ tailWord_150536) baseStart_150536 baseEnd_150536 := by
    simpa [prefixWord, tailWord_150536, baseEnd_150536] using wordTrace_append hprefix tailTrace_150536
  have hstable : (prefixWord ++ tailWord_150536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150536).length < 2 ^ (prefixWord ++ tailWord_150536).sum := by decide
  have hdescent : baseEnd_150536 < baseStart_150536 := by decide
  rcases family_descends (prefixWord ++ tailWord_150536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150551 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 6]
def baseStart_150551 : Nat := 118140960795 + 150551 * 2 ^ 59
def prefixEnd_150551 : Nat := 4983230072969 + 3 ^ 40 * 150551 * 2
def baseEnd_150551 : Nat := 17178894670032378271141

theorem tailTrace_150551 : CollatzResearch.WordTrace tailWord_150551 prefixEnd_150551 17178894670032378271141 := by
  unfold tailWord_150551
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491046077586913908867507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3660697385057942605911671 5491046077586913908867507)
  ·
    refine ⟨8236569116380370863301261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5491046077586913908867507 8236569116380370863301261)
    ·
      refine ⟨3088713418642639073737973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8236569116380370863301261 3088713418642639073737973)
      ·
        refine ⟨289566882997747413162935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3088713418642639073737973 289566882997747413162935)
        ·
          refine ⟨434350324496621119744403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289566882997747413162935 434350324496621119744403)
          ·
            refine ⟨651525486744931679616605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434350324496621119744403 651525486744931679616605)
            ·
              refine ⟨244322057529349379856227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 651525486744931679616605 244322057529349379856227)
              ·
                refine ⟨366483086294024069784341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244322057529349379856227 366483086294024069784341)
                ·
                  refine ⟨17178894670032378271141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 366483086294024069784341 17178894670032378271141)
                  ·
                    rfl

theorem cell22_150551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 6].length) (baseStart_150551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150551 prefixEnd_150551 := by exact prefixLift 150551
  have htrace : WordTrace (prefixWord ++ tailWord_150551) baseStart_150551 baseEnd_150551 := by
    simpa [prefixWord, tailWord_150551, baseEnd_150551] using wordTrace_append hprefix tailTrace_150551
  have hstable : (prefixWord ++ tailWord_150551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150551).length < 2 ^ (prefixWord ++ tailWord_150551).sum := by decide
  have hdescent : baseEnd_150551 < baseStart_150551 := by decide
  rcases family_descends (prefixWord ++ tailWord_150551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150570 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_150570 : Nat := 118140960795 + 150570 * 2 ^ 59
def prefixEnd_150570 : Nat := 4983230072969 + 3 ^ 40 * 150570 * 2
def baseEnd_150570 : Nat := 51543188098387418588365

theorem tailTrace_150570 : CollatzResearch.WordTrace tailWord_150570 prefixEnd_150570 51543188098387418588365 := by
  unfold tailWord_150570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372934766129520038452291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3661159376345386769206109 1372934766129520038452291)
  ·
    refine ⟨2059402149194280057678437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1372934766129520038452291 2059402149194280057678437)
    ·
      refine ⟨386137902973927510814707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2059402149194280057678437 386137902973927510814707)
      ·
        refine ⟨579206854460891266222061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386137902973927510814707 579206854460891266222061)
        ·
          refine ⟨217202570422834224833273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 579206854460891266222061 217202570422834224833273)
          ·
            refine ⟨162901927817125668624955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217202570422834224833273 162901927817125668624955)
            ·
              refine ⟨244352891725688502937433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162901927817125668624955 244352891725688502937433)
              ·
                refine ⟨183264668794266377203075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244352891725688502937433 183264668794266377203075)
                ·
                  refine ⟨274897003191399565804613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183264668794266377203075 274897003191399565804613)
                  ·
                    refine ⟨51543188098387418588365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274897003191399565804613 51543188098387418588365)
                    ·
                      rfl

theorem cell22_150570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_150570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150570 prefixEnd_150570 := by exact prefixLift 150570
  have htrace : WordTrace (prefixWord ++ tailWord_150570) baseStart_150570 baseEnd_150570 := by
    simpa [prefixWord, tailWord_150570, baseEnd_150570] using wordTrace_append hprefix tailTrace_150570
  have hstable : (prefixWord ++ tailWord_150570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150570).length < 2 ^ (prefixWord ++ tailWord_150570).sum := by decide
  have hdescent : baseEnd_150570 < baseStart_150570 := by decide
  rcases family_descends (prefixWord ++ tailWord_150570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150609 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_150609 : Nat := 118140960795 + 150609 * 2 ^ 59
def prefixEnd_150609 : Nat := 4983230072969 + 3 ^ 40 * 150609 * 2
def baseEnd_150609 : Nat := 51556538595404316863245

theorem tailTrace_150609 : CollatzResearch.WordTrace tailWord_150609 prefixEnd_150609 51556538595404316863245 := by
  unfold tailWord_150609
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493161511376789814478881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3662107674251193209652587 5493161511376789814478881)
  ·
    refine ⟨4119871133532592360859161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5493161511376789814478881 4119871133532592360859161)
    ·
      refine ⟨3089903350149444270644371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4119871133532592360859161 3089903350149444270644371)
      ·
        refine ⟨4634855025224166405966557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089903350149444270644371 4634855025224166405966557)
        ·
          refine ⟨1738070634459062402237459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4634855025224166405966557 1738070634459062402237459)
          ·
            refine ⟨2607105951688593603356189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738070634459062402237459 2607105951688593603356189)
            ·
              refine ⟨977664731883222601258571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2607105951688593603356189 977664731883222601258571)
              ·
                refine ⟨1466497097824833901887857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977664731883222601258571 1466497097824833901887857)
                ·
                  refine ⟨1099872823368625426415893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1466497097824833901887857 1099872823368625426415893)
                  ·
                    refine ⟨51556538595404316863245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1099872823368625426415893 51556538595404316863245)
                    ·
                      rfl

theorem cell22_150609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_150609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150609 prefixEnd_150609 := by exact prefixLift 150609
  have htrace : WordTrace (prefixWord ++ tailWord_150609) baseStart_150609 baseEnd_150609 := by
    simpa [prefixWord, tailWord_150609, baseEnd_150609] using wordTrace_append hprefix tailTrace_150609
  have hstable : (prefixWord ++ tailWord_150609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150609).length < 2 ^ (prefixWord ++ tailWord_150609).sum := by decide
  have hdescent : baseEnd_150609 < baseStart_150609 := by decide
  rcases family_descends (prefixWord ++ tailWord_150609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150632 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 2, 4]
def baseStart_150632 : Nat := 118140960795 + 150632 * 2 ^ 59
def prefixEnd_150632 : Nat := 4983230072969 + 3 ^ 40 * 150632 * 2
def baseEnd_150632 : Nat := 51564411965439923538175

theorem tailTrace_150632 : CollatzResearch.WordTrace tailWord_150632 prefixEnd_150632 51564411965439923538175 := by
  unfold tailWord_150632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747000195146732371283075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3662666926862309828377433 2747000195146732371283075)
  ·
    refine ⟨4120500292720098556924613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2747000195146732371283075 4120500292720098556924613)
    ·
      refine ⟨772593804885018479423365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4120500292720098556924613 772593804885018479423365)
      ·
        refine ⟨144861338415940964891881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 772593804885018479423365 144861338415940964891881)
        ·
          refine ⟨108646003811955723668911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144861338415940964891881 108646003811955723668911)
          ·
            refine ⟨162969005717933585503367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108646003811955723668911 162969005717933585503367)
            ·
              refine ⟨244453508576900378255051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162969005717933585503367 244453508576900378255051)
              ·
                refine ⟨366680262865350567382577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244453508576900378255051 366680262865350567382577)
                ·
                  refine ⟨275010197149012925536933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366680262865350567382577 275010197149012925536933)
                  ·
                    refine ⟨51564411965439923538175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 275010197149012925536933 51564411965439923538175)
                    ·
                      rfl

theorem cell22_150632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_150632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150632 prefixEnd_150632 := by exact prefixLift 150632
  have htrace : WordTrace (prefixWord ++ tailWord_150632) baseStart_150632 baseEnd_150632 := by
    simpa [prefixWord, tailWord_150632, baseEnd_150632] using wordTrace_append hprefix tailTrace_150632
  have hstable : (prefixWord ++ tailWord_150632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150632).length < 2 ^ (prefixWord ++ tailWord_150632).sum := by decide
  have hdescent : baseEnd_150632 < baseStart_150632 := by decide
  rcases family_descends (prefixWord ++ tailWord_150632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150639 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 1, 7]
def baseStart_150639 : Nat := 118140960795 + 150639 * 2 ^ 59
def prefixEnd_150639 : Nat := 4983230072969 + 3 ^ 40 * 150639 * 2
def baseEnd_150639 : Nat := 51566808208494238613153

theorem tailTrace_150639 : CollatzResearch.WordTrace tailWord_150639 prefixEnd_150639 51566808208494238613153 := by
  unfold tailWord_150639
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494255701268104938070971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3662837134178736625380647 5494255701268104938070971)
  ·
    refine ⟨8241383551902157407106457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5494255701268104938070971 8241383551902157407106457)
    ·
      refine ⟨6181037663926618055329843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8241383551902157407106457 6181037663926618055329843)
      ·
        refine ⟨9271556495889927082994765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6181037663926618055329843 9271556495889927082994765)
        ·
          refine ⟨3476833685958722656123037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9271556495889927082994765 3476833685958722656123037)
          ·
            refine ⟨1303812632234520996046139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3476833685958722656123037 1303812632234520996046139)
            ·
              refine ⟨1955718948351781494069209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303812632234520996046139 1955718948351781494069209)
              ·
                refine ⟨1466789211263836120551907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955718948351781494069209 1466789211263836120551907)
                ·
                  refine ⟨2200183816895754180827861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466789211263836120551907 2200183816895754180827861)
                  ·
                    refine ⟨51566808208494238613153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2200183816895754180827861 51566808208494238613153)
                    ·
                      rfl

theorem cell22_150639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_150639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150639 prefixEnd_150639 := by exact prefixLift 150639
  have htrace : WordTrace (prefixWord ++ tailWord_150639) baseStart_150639 baseEnd_150639 := by
    simpa [prefixWord, tailWord_150639, baseEnd_150639] using wordTrace_append hprefix tailTrace_150639
  have hstable : (prefixWord ++ tailWord_150639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150639).length < 2 ^ (prefixWord ++ tailWord_150639).sum := by decide
  have hdescent : baseEnd_150639 < baseStart_150639 := by decide
  rcases family_descends (prefixWord ++ tailWord_150639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150688 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_150688 : Nat := 118140960795 + 150688 * 2 ^ 59
def prefixEnd_150688 : Nat := 4983230072969 + 3 ^ 40 * 150688 * 2
def baseEnd_150688 : Nat := 51583581909874444138003

theorem tailTrace_150688 : CollatzResearch.WordTrace tailWord_150688 prefixEnd_150688 51583581909874444138003 := by
  unfold tailWord_150688
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748021439045293153302359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3664028585393724204403145 2748021439045293153302359)
  ·
    refine ⟨4122032158567939729953539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748021439045293153302359 4122032158567939729953539)
    ·
      refine ⟨6183048237851909594930309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4122032158567939729953539 6183048237851909594930309)
      ·
        refine ⟨1159321544597233049049433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6183048237851909594930309 1159321544597233049049433)
        ·
          refine ⟨869491158447924786787075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159321544597233049049433 869491158447924786787075)
          ·
            refine ⟨1304236737671887180180613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869491158447924786787075 1304236737671887180180613)
            ·
              refine ⟨244544388313478846283865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1304236737671887180180613 244544388313478846283865)
              ·
                refine ⟨183408291235109134712899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244544388313478846283865 183408291235109134712899)
                ·
                  refine ⟨275112436852663702069349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183408291235109134712899 275112436852663702069349)
                  ·
                    refine ⟨51583581909874444138003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 275112436852663702069349 51583581909874444138003)
                    ·
                      rfl

theorem cell22_150688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_150688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150688 prefixEnd_150688 := by exact prefixLift 150688
  have htrace : WordTrace (prefixWord ++ tailWord_150688) baseStart_150688 baseEnd_150688 := by
    simpa [prefixWord, tailWord_150688, baseEnd_150688] using wordTrace_append hprefix tailTrace_150688
  have hstable : (prefixWord ++ tailWord_150688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150688).length < 2 ^ (prefixWord ++ tailWord_150688).sum := by decide
  have hdescent : baseEnd_150688 < baseStart_150688 := by decide
  rcases family_descends (prefixWord ++ tailWord_150688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150703 : List Nat := [1, 1, 2, 1, 2, 3, 5, 3, 4]
def baseStart_150703 : Nat := 118140960795 + 150703 * 2 ^ 59
def prefixEnd_150703 : Nat := 4983230072969 + 3 ^ 40 * 150703 * 2
def baseEnd_150703 : Nat := 17196238905473135004319

theorem tailTrace_150703 : CollatzResearch.WordTrace tailWord_150703 prefixEnd_150703 17196238905473135004319 := by
  unfold tailWord_150703
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496589973036243868400763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3664393315357495912267175 5496589973036243868400763)
  ·
    refine ⟨8244884959554365802601145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5496589973036243868400763 8244884959554365802601145)
    ·
      refine ⟨6183663719665774351950859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8244884959554365802601145 6183663719665774351950859)
      ·
        refine ⟨9275495579498661527926289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183663719665774351950859 9275495579498661527926289)
        ·
          refine ⟨6956621684623996145944717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9275495579498661527926289 6956621684623996145944717)
          ·
            refine ⟨2608733131733998554729269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6956621684623996145944717 2608733131733998554729269)
            ·
              refine ⟨244568731100062364505869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2608733131733998554729269 244568731100062364505869)
              ·
                refine ⟨91713274162523386689701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244568731100062364505869 91713274162523386689701)
                ·
                  refine ⟨17196238905473135004319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91713274162523386689701 17196238905473135004319)
                  ·
                    rfl

theorem cell22_150703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 4].length) (baseStart_150703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150703 prefixEnd_150703 := by exact prefixLift 150703
  have htrace : WordTrace (prefixWord ++ tailWord_150703) baseStart_150703 baseEnd_150703 := by
    simpa [prefixWord, tailWord_150703, baseEnd_150703] using wordTrace_append hprefix tailTrace_150703
  have hstable : (prefixWord ++ tailWord_150703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150703).length < 2 ^ (prefixWord ++ tailWord_150703).sum := by decide
  have hdescent : baseEnd_150703 < baseStart_150703 := by decide
  rcases family_descends (prefixWord ++ tailWord_150703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150720 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 6]
def baseStart_150720 : Nat := 118140960795 + 150720 * 2 ^ 59
def prefixEnd_150720 : Nat := 4983230072969 + 3 ^ 40 * 150720 * 2
def baseEnd_150720 : Nat := 17198178721279009112635

theorem tailTrace_150720 : CollatzResearch.WordTrace tailWord_150720 prefixEnd_150720 17198178721279009112635 := by
  unfold tailWord_150720
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748605006987327885884807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3664806675983103847846409 2748605006987327885884807)
  ·
    refine ⟨4122907510480991828827211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748605006987327885884807 4122907510480991828827211)
    ·
      refine ⟨6184361265721487743240817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4122907510480991828827211 6184361265721487743240817)
      ·
        refine ⟨4638270949291115807430613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6184361265721487743240817 4638270949291115807430613)
        ·
          refine ⟨108709475374010526736655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4638270949291115807430613 108709475374010526736655)
          ·
            refine ⟨163064213061015790104983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108709475374010526736655 163064213061015790104983)
            ·
              refine ⟨244596319591523685157475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163064213061015790104983 244596319591523685157475)
              ·
                refine ⟨366894479387285527736213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244596319591523685157475 366894479387285527736213)
                ·
                  refine ⟨17198178721279009112635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 366894479387285527736213 17198178721279009112635)
                  ·
                    rfl

theorem cell22_150720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_150720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150720 prefixEnd_150720 := by exact prefixLift 150720
  have htrace : WordTrace (prefixWord ++ tailWord_150720) baseStart_150720 baseEnd_150720 := by
    simpa [prefixWord, tailWord_150720, baseEnd_150720] using wordTrace_append hprefix tailTrace_150720
  have hstable : (prefixWord ++ tailWord_150720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150720).length < 2 ^ (prefixWord ++ tailWord_150720).sum := by decide
  have hdescent : baseEnd_150720 < baseStart_150720 := by decide
  rcases family_descends (prefixWord ++ tailWord_150720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150726 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_150726 : Nat := 118140960795 + 150726 * 2 ^ 59
def prefixEnd_150726 : Nat := 4983230072969 + 3 ^ 40 * 150726 * 2
def baseEnd_150726 : Nat := 17198863362151670562629

theorem tailTrace_150726 : CollatzResearch.WordTrace tailWord_150726 prefixEnd_150726 17198863362151670562629 := by
  unfold tailWord_150726
  simp only [CollatzResearch.WordTrace]
  refine ⟨171794651623528712390251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3664952567968612530992021 171794651623528712390251)
  ·
    refine ⟨257691977435293068585377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171794651623528712390251 257691977435293068585377)
    ·
      refine ⟨193268983076469801439033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257691977435293068585377 193268983076469801439033)
      ·
        refine ⟨144951737307352351079275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193268983076469801439033 144951737307352351079275)
        ·
          refine ⟨217427605961028526618913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144951737307352351079275 217427605961028526618913)
          ·
            refine ⟨163070704470771394964185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217427605961028526618913 163070704470771394964185)
            ·
              refine ⟨122303028353078546223139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163070704470771394964185 122303028353078546223139)
              ·
                refine ⟨183454542529617819334709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122303028353078546223139 183454542529617819334709)
                ·
                  refine ⟨17198863362151670562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183454542529617819334709 17198863362151670562629)
                  ·
                    rfl

theorem cell22_150726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_150726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150726 prefixEnd_150726 := by exact prefixLift 150726
  have htrace : WordTrace (prefixWord ++ tailWord_150726) baseStart_150726 baseEnd_150726 := by
    simpa [prefixWord, tailWord_150726, baseEnd_150726] using wordTrace_append hprefix tailTrace_150726
  have hstable : (prefixWord ++ tailWord_150726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150726).length < 2 ^ (prefixWord ++ tailWord_150726).sum := by decide
  have hdescent : baseEnd_150726 < baseStart_150726 := by decide
  rcases family_descends (prefixWord ++ tailWord_150726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150868 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_150868 : Nat := 118140960795 + 150868 * 2 ^ 59
def prefixEnd_150868 : Nat := 4983230072969 + 3 ^ 40 * 150868 * 2
def baseEnd_150868 : Nat := 51645199588413974637451

theorem tailTrace_150868 : CollatzResearch.WordTrace tailWord_150868 prefixEnd_150868 51645199588413974637451 := by
  unfold tailWord_150868
  simp only [CollatzResearch.WordTrace]
  refine ⟨2751304008719238524078629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3668405344958984698771505 2751304008719238524078629)
  ·
    refine ⟨515869501634857223264743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2751304008719238524078629 515869501634857223264743)
    ·
      refine ⟨773804252452285834897115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515869501634857223264743 773804252452285834897115)
      ·
        refine ⟨1160706378678428752345673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773804252452285834897115 1160706378678428752345673)
        ·
          refine ⟨870529784008821564259255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1160706378678428752345673 870529784008821564259255)
          ·
            refine ⟨1305794676013232346388883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870529784008821564259255 1305794676013232346388883)
            ·
              refine ⟨1958692014019848519583325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305794676013232346388883 1958692014019848519583325)
              ·
                refine ⟨734509505257443194843747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1958692014019848519583325 734509505257443194843747)
                ·
                  refine ⟨1101764257886164792265621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734509505257443194843747 1101764257886164792265621)
                  ·
                    refine ⟨51645199588413974637451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1101764257886164792265621 51645199588413974637451)
                    ·
                      rfl

theorem cell22_150868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_150868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150868 prefixEnd_150868 := by exact prefixLift 150868
  have htrace : WordTrace (prefixWord ++ tailWord_150868) baseStart_150868 baseEnd_150868 := by
    simpa [prefixWord, tailWord_150868, baseEnd_150868] using wordTrace_append hprefix tailTrace_150868
  have hstable : (prefixWord ++ tailWord_150868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150868).length < 2 ^ (prefixWord ++ tailWord_150868).sum := by decide
  have hdescent : baseEnd_150868 < baseStart_150868 := by decide
  rcases family_descends (prefixWord ++ tailWord_150868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150883 : List Nat := [1, 1, 1, 5, 2, 4, 8]
def baseStart_150883 : Nat := 118140960795 + 150883 * 2 ^ 59
def prefixEnd_150883 : Nat := 4983230072969 + 3 ^ 40 * 150883 * 2
def baseEnd_150883 : Nat := 1912975347961442056015

theorem tailTrace_150883 : CollatzResearch.WordTrace tailWord_150883 prefixEnd_150883 1912975347961442056015 := by
  unfold tailWord_150883
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503155112384134609953303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3668770074922756406635535 5503155112384134609953303)
  ·
    refine ⟨8254732668576201914929955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5503155112384134609953303 8254732668576201914929955)
    ·
      refine ⟨12382099002864302872394933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8254732668576201914929955 12382099002864302872394933)
      ·
        refine ⟨1160821781518528394287025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12382099002864302872394933 1160821781518528394287025)
        ·
          refine ⟨870616336138896295715269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1160821781518528394287025 870616336138896295715269)
          ·
            refine ⟨163240563026043055446613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 870616336138896295715269 163240563026043055446613)
            ·
              refine ⟨1912975347961442056015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 163240563026043055446613 1912975347961442056015)
              ·
                rfl

theorem cell22_150883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 8].length) (baseStart_150883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_150883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_150883 prefixEnd_150883 := by exact prefixLift 150883
  have htrace : WordTrace (prefixWord ++ tailWord_150883) baseStart_150883 baseEnd_150883 := by
    simpa [prefixWord, tailWord_150883, baseEnd_150883] using wordTrace_append hprefix tailTrace_150883
  have hstable : (prefixWord ++ tailWord_150883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150883).length < 2 ^ (prefixWord ++ tailWord_150883).sum := by decide
  have hdescent : baseEnd_150883 < baseStart_150883 := by decide
  rcases family_descends (prefixWord ++ tailWord_150883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151033 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_151033 : Nat := 118140960795 + 151033 * 2 ^ 59
def prefixEnd_151033 : Nat := 4983230072969 + 3 ^ 40 * 151033 * 2
def baseEnd_151033 : Nat := 51701682460408544261945

theorem tailTrace_151033 : CollatzResearch.WordTrace tailWord_151033 prefixEnd_151033 51701682460408544261945 := by
  unfold tailWord_151033
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508626061840710227913753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3672417374560473485275835 5508626061840710227913753)
  ·
    refine ⟨4131469546380532670935315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5508626061840710227913753 4131469546380532670935315)
    ·
      refine ⟨6197204319570799006402973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4131469546380532670935315 6197204319570799006402973)
      ·
        refine ⟨2323951619839049627401115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6197204319570799006402973 2323951619839049627401115)
        ·
          refine ⟨3485927429758574441101673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323951619839049627401115 3485927429758574441101673)
          ·
            refine ⟨2614445572318930830826255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3485927429758574441101673 2614445572318930830826255)
            ·
              refine ⟨3921668358478396246239383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614445572318930830826255 3921668358478396246239383)
              ·
                refine ⟨5882502537717594369359075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3921668358478396246239383 5882502537717594369359075)
                ·
                  refine ⟨8823753806576391554038613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5882502537717594369359075 8823753806576391554038613)
                  ·
                    refine ⟨51701682460408544261945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 8823753806576391554038613 51701682460408544261945)
                    ·
                      rfl

theorem cell22_151033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_151033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151033 prefixEnd_151033 := by exact prefixLift 151033
  have htrace : WordTrace (prefixWord ++ tailWord_151033) baseStart_151033 baseEnd_151033 := by
    simpa [prefixWord, tailWord_151033, baseEnd_151033] using wordTrace_append hprefix tailTrace_151033
  have hstable : (prefixWord ++ tailWord_151033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151033).length < 2 ^ (prefixWord ++ tailWord_151033).sum := by decide
  have hdescent : baseEnd_151033 < baseStart_151033 := by decide
  rcases family_descends (prefixWord ++ tailWord_151033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151041 : List Nat := [1, 2, 4, 1, 5, 1, 1, 3, 4]
def baseStart_151041 : Nat := 118140960795 + 151041 * 2 ^ 59
def prefixEnd_151041 : Nat := 4983230072969 + 3 ^ 40 * 151041 * 2
def baseEnd_151041 : Nat := 17234807007966396687307

theorem tailTrace_151041 : CollatzResearch.WordTrace tailWord_151041 prefixEnd_151041 17234807007966396687307 := by
  unfold tailWord_151041
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508917845811727594204977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3672611897207818396136651 5508917845811727594204977)
  ·
    refine ⟨4131688384358795695653733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5508917845811727594204977 4131688384358795695653733)
    ·
      refine ⟨774691572067274192935075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4131688384358795695653733 774691572067274192935075)
      ·
        refine ⟨1162037358100911289402613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774691572067274192935075 1162037358100911289402613)
        ·
          refine ⟨108941002321960433381495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1162037358100911289402613 108941002321960433381495)
          ·
            refine ⟨163411503482940650072243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108941002321960433381495 163411503482940650072243)
            ·
              refine ⟨245117255224410975108365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163411503482940650072243 245117255224410975108365)
              ·
                refine ⟨91918970709154115665637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245117255224410975108365 91918970709154115665637)
                ·
                  refine ⟨17234807007966396687307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91918970709154115665637 17234807007966396687307)
                  ·
                    rfl

theorem cell22_151041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_151041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151041 prefixEnd_151041 := by exact prefixLift 151041
  have htrace : WordTrace (prefixWord ++ tailWord_151041) baseStart_151041 baseEnd_151041 := by
    simpa [prefixWord, tailWord_151041, baseEnd_151041] using wordTrace_append hprefix tailTrace_151041
  have hstable : (prefixWord ++ tailWord_151041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151041).length < 2 ^ (prefixWord ++ tailWord_151041).sum := by decide
  have hdescent : baseEnd_151041 < baseStart_151041 := by decide
  rcases family_descends (prefixWord ++ tailWord_151041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151052 : List Nat := [2, 2, 1, 2, 6, 1, 8]
def baseStart_151052 : Nat := 118140960795 + 151052 * 2 ^ 59
def prefixEnd_151052 : Nat := 4983230072969 + 3 ^ 40 * 151052 * 2
def baseEnd_151052 : Nat := 1915118020322178816181

theorem tailTrace_151052 : CollatzResearch.WordTrace tailWord_151052 prefixEnd_151052 1915118020322178816181 := by
  unfold tailWord_151052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754659524385938236427705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3672879365847917648570273 2754659524385938236427705)
  ·
    refine ⟨2065994643289453677320779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2754659524385938236427705 2065994643289453677320779)
    ·
      refine ⟨3098991964934180515981169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065994643289453677320779 3098991964934180515981169)
      ·
        refine ⟨2324243973700635386985877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3098991964934180515981169 2324243973700635386985877)
        ·
          refine ⟨108948936267217283764963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2324243973700635386985877 108948936267217283764963)
          ·
            refine ⟨163423404400825925647445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108948936267217283764963 163423404400825925647445)
            ·
              refine ⟨1915118020322178816181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 163423404400825925647445 1915118020322178816181)
              ·
                rfl

theorem cell22_151052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 8].length) (baseStart_151052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151052 prefixEnd_151052 := by exact prefixLift 151052
  have htrace : WordTrace (prefixWord ++ tailWord_151052) baseStart_151052 baseEnd_151052 := by
    simpa [prefixWord, tailWord_151052, baseEnd_151052] using wordTrace_append hprefix tailTrace_151052
  have hstable : (prefixWord ++ tailWord_151052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151052).length < 2 ^ (prefixWord ++ tailWord_151052).sum := by decide
  have hdescent : baseEnd_151052 < baseStart_151052 := by decide
  rcases family_descends (prefixWord ++ tailWord_151052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151125 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 6]
def baseStart_151125 : Nat := 118140960795 + 151125 * 2 ^ 59
def prefixEnd_151125 : Nat := 4983230072969 + 3 ^ 40 * 151125 * 2
def baseEnd_151125 : Nat := 17244391980183656987221

theorem tailTrace_151125 : CollatzResearch.WordTrace tailWord_151125 prefixEnd_151125 17244391980183656987221 := by
  unfold tailWord_151125
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511981577507409940262829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3674654385004939960175219 5511981577507409940262829)
  ·
    refine ⟨2066993091565278727598561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5511981577507409940262829 2066993091565278727598561)
    ·
      refine ⟨1550244818673959045698921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2066993091565278727598561 1550244818673959045698921)
      ·
        refine ⟨1162683614005469284274191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1550244818673959045698921 1162683614005469284274191)
        ·
          refine ⟨1744025421008203926411287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162683614005469284274191 1744025421008203926411287)
          ·
            refine ⟨2616038131512305889616931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744025421008203926411287 2616038131512305889616931)
            ·
              refine ⟨3924057197268458834425397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616038131512305889616931 3924057197268458834425397)
              ·
                refine ⟨367880362243918015727381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3924057197268458834425397 367880362243918015727381)
                ·
                  refine ⟨17244391980183656987221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 367880362243918015727381 17244391980183656987221)
                  ·
                    rfl

theorem cell22_151125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_151125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151125 prefixEnd_151125 := by exact prefixLift 151125
  have htrace : WordTrace (prefixWord ++ tailWord_151125) baseStart_151125 baseEnd_151125 := by
    simpa [prefixWord, tailWord_151125, baseEnd_151125] using wordTrace_append hprefix tailTrace_151125
  have hstable : (prefixWord ++ tailWord_151125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151125).length < 2 ^ (prefixWord ++ tailWord_151125).sum := by decide
  have hdescent : baseEnd_151125 < baseStart_151125 := by decide
  rcases family_descends (prefixWord ++ tailWord_151125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151191 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 2, 3]
def baseStart_151191 : Nat := 118140960795 + 151191 * 2 ^ 59
def prefixEnd_151191 : Nat := 4983230072969 + 3 ^ 40 * 151191 * 2
def baseEnd_151191 : Nat := 51755769089348798811461

theorem tailTrace_151191 : CollatzResearch.WordTrace tailWord_151191 prefixEnd_151191 51755769089348798811461 := by
  unfold tailWord_151191
  simp only [CollatzResearch.WordTrace]
  refine ⟨5514388795268303212165427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3676259196845535474776951 5514388795268303212165427)
  ·
    refine ⟨8271583192902454818248141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5514388795268303212165427 8271583192902454818248141)
    ·
      refine ⟨3101843697338420556843053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8271583192902454818248141 3101843697338420556843053)
      ·
        refine ⟨1163191386501907708816145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3101843697338420556843053 1163191386501907708816145)
        ·
          refine ⟨872393539876430781612109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163191386501907708816145 872393539876430781612109)
          ·
            refine ⟨327147577453661543104541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 872393539876430781612109 327147577453661543104541)
            ·
              refine ⟨122680341545123078664203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327147577453661543104541 122680341545123078664203)
              ·
                refine ⟨184020512317684617996305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122680341545123078664203 184020512317684617996305)
                ·
                  refine ⟨138015384238263463497229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184020512317684617996305 138015384238263463497229)
                  ·
                    refine ⟨51755769089348798811461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138015384238263463497229 51755769089348798811461)
                    ·
                      rfl

theorem cell22_151191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_151191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151191 prefixEnd_151191 := by exact prefixLift 151191
  have htrace : WordTrace (prefixWord ++ tailWord_151191) baseStart_151191 baseEnd_151191 := by
    simpa [prefixWord, tailWord_151191, baseEnd_151191] using wordTrace_append hprefix tailTrace_151191
  have hstable : (prefixWord ++ tailWord_151191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151191).length < 2 ^ (prefixWord ++ tailWord_151191).sum := by decide
  have hdescent : baseEnd_151191 < baseStart_151191 := by decide
  rcases family_descends (prefixWord ++ tailWord_151191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151204 : List Nat := [2, 3, 1, 2, 2, 4, 2, 6]
def baseStart_151204 : Nat := 118140960795 + 151204 * 2 ^ 59
def prefixEnd_151204 : Nat := 4983230072969 + 3 ^ 40 * 151204 * 2
def baseEnd_151204 : Nat := 5751135472780122026269

theorem tailTrace_151204 : CollatzResearch.WordTrace tailWord_151204 prefixEnd_151204 5751135472780122026269 := by
  unfold tailWord_151204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757431472110603216194333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3676575296147470954925777 2757431472110603216194333)
  ·
    refine ⟨1034036802041476206072875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2757431472110603216194333 1034036802041476206072875)
    ·
      refine ⟨1551055203062214309109313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034036802041476206072875 1551055203062214309109313)
      ·
        refine ⟨1163291402296660731831985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1551055203062214309109313 1163291402296660731831985)
        ·
          refine ⟨872468551722495548873989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163291402296660731831985 872468551722495548873989)
          ·
            refine ⟨163587853447967915413873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 872468551722495548873989 163587853447967915413873)
            ·
              refine ⟨122690890085975936560405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163587853447967915413873 122690890085975936560405)
              ·
                refine ⟨5751135472780122026269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122690890085975936560405 5751135472780122026269)
                ·
                  rfl

theorem cell22_151204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 6].length) (baseStart_151204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151204 prefixEnd_151204 := by exact prefixLift 151204
  have htrace : WordTrace (prefixWord ++ tailWord_151204) baseStart_151204 baseEnd_151204 := by
    simpa [prefixWord, tailWord_151204, baseEnd_151204] using wordTrace_append hprefix tailTrace_151204
  have hstable : (prefixWord ++ tailWord_151204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151204).length < 2 ^ (prefixWord ++ tailWord_151204).sum := by decide
  have hdescent : baseEnd_151204 < baseStart_151204 := by decide
  rcases family_descends (prefixWord ++ tailWord_151204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151215 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 9]
def baseStart_151215 : Nat := 118140960795 + 151215 * 2 ^ 59
def prefixEnd_151215 : Nat := 4983230072969 + 3 ^ 40 * 151215 * 2
def baseEnd_151215 : Nat := 17254661593273578737129

theorem tailTrace_151215 : CollatzResearch.WordTrace tailWord_151215 prefixEnd_151215 17254661593273578737129 := by
  unfold tailWord_151215
  simp only [CollatzResearch.WordTrace]
  refine ⟨5515264147181355311039099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3676842764787570207359399 5515264147181355311039099)
  ·
    refine ⟨8272896220772032966558649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5515264147181355311039099 8272896220772032966558649)
    ·
      refine ⟨6204672165579024724918987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8272896220772032966558649 6204672165579024724918987)
      ·
        refine ⟨9307008248368537087378481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6204672165579024724918987 9307008248368537087378481)
        ·
          refine ⟨6980256186276402815533861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9307008248368537087378481 6980256186276402815533861)
          ·
            refine ⟨1308798034926825527912599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6980256186276402815533861 1308798034926825527912599)
            ·
              refine ⟨1963197052390238291868899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308798034926825527912599 1963197052390238291868899)
              ·
                refine ⟨2944795578585357437803349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963197052390238291868899 2944795578585357437803349)
                ·
                  refine ⟨17254661593273578737129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2944795578585357437803349 17254661593273578737129)
                  ·
                    rfl

theorem cell22_151215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 9].length) (baseStart_151215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151215 prefixEnd_151215 := by exact prefixLift 151215
  have htrace : WordTrace (prefixWord ++ tailWord_151215) baseStart_151215 baseEnd_151215 := by
    simpa [prefixWord, tailWord_151215, baseEnd_151215] using wordTrace_append hprefix tailTrace_151215
  have hstable : (prefixWord ++ tailWord_151215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151215).length < 2 ^ (prefixWord ++ tailWord_151215).sum := by decide
  have hdescent : baseEnd_151215 < baseStart_151215 := by decide
  rcases family_descends (prefixWord ++ tailWord_151215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151232 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 5]
def baseStart_151232 : Nat := 118140960795 + 151232 * 2 ^ 59
def prefixEnd_151232 : Nat := 4983230072969 + 3 ^ 40 * 151232 * 2
def baseEnd_151232 : Nat := 17256601409079452845445

theorem tailTrace_151232 : CollatzResearch.WordTrace tailWord_151232 prefixEnd_151232 17256601409079452845445 := by
  unfold tailWord_151232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757942094059883607203975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3677256125413178142938633 2757942094059883607203975)
  ·
    refine ⟨4136913141089825410805963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2757942094059883607203975 4136913141089825410805963)
    ·
      refine ⟨6205369711634738116208945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4136913141089825410805963 6205369711634738116208945)
      ·
        refine ⟨4654027283726053587156709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6205369711634738116208945 4654027283726053587156709)
        ·
          refine ⟨872630115698635047591883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4654027283726053587156709 872630115698635047591883)
          ·
            refine ⟨1308945173547952571387825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872630115698635047591883 1308945173547952571387825)
            ·
              refine ⟨981708880160964428540869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308945173547952571387825 981708880160964428540869)
              ·
                refine ⟨184070415030180830351413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 981708880160964428540869 184070415030180830351413)
                ·
                  refine ⟨17256601409079452845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184070415030180830351413 17256601409079452845445)
                  ·
                    rfl

theorem cell22_151232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_151232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151232 prefixEnd_151232 := by exact prefixLift 151232
  have htrace : WordTrace (prefixWord ++ tailWord_151232) baseStart_151232 baseEnd_151232 := by
    simpa [prefixWord, tailWord_151232, baseEnd_151232] using wordTrace_append hprefix tailTrace_151232
  have hstable : (prefixWord ++ tailWord_151232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151232).length < 2 ^ (prefixWord ++ tailWord_151232).sum := by decide
  have hdescent : baseEnd_151232 < baseStart_151232 := by decide
  rcases family_descends (prefixWord ++ tailWord_151232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151249 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 5]
def baseStart_151249 : Nat := 118140960795 + 151249 * 2 ^ 59
def prefixEnd_151249 : Nat := 4983230072969 + 3 ^ 40 * 151249 * 2
def baseEnd_151249 : Nat := 17258541224885326953761

theorem tailTrace_151249 : CollatzResearch.WordTrace tailWord_151249 prefixEnd_151249 17258541224885326953761 := by
  unfold tailWord_151249
  simp only [CollatzResearch.WordTrace]
  refine ⟨5516504229058179117776801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3677669486038786078517867 5516504229058179117776801)
  ·
    refine ⟨4137378171793634338332601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5516504229058179117776801 4137378171793634338332601)
    ·
      refine ⟨3103033628845225753749451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4137378171793634338332601 3103033628845225753749451)
      ·
        refine ⟨4654550443267838630624177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103033628845225753749451 4654550443267838630624177)
        ·
          refine ⟨3490912832450878972968133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4654550443267838630624177 3490912832450878972968133)
          ·
            refine ⟨654546156084539807431525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3490912832450878972968133 654546156084539807431525)
            ·
              refine ⟨122727404265851213893411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 654546156084539807431525 122727404265851213893411)
              ·
                refine ⟨184091106398776820840117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122727404265851213893411 184091106398776820840117)
                ·
                  refine ⟨17258541224885326953761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184091106398776820840117 17258541224885326953761)
                  ·
                    rfl

theorem cell22_151249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_151249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151249 prefixEnd_151249 := by exact prefixLift 151249
  have htrace : WordTrace (prefixWord ++ tailWord_151249) baseStart_151249 baseEnd_151249 := by
    simpa [prefixWord, tailWord_151249, baseEnd_151249] using wordTrace_append hprefix tailTrace_151249
  have hstable : (prefixWord ++ tailWord_151249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151249).length < 2 ^ (prefixWord ++ tailWord_151249).sum := by decide
  have hdescent : baseEnd_151249 < baseStart_151249 := by decide
  rcases family_descends (prefixWord ++ tailWord_151249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151292 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_151292 : Nat := 118140960795 + 151292 * 2 ^ 59
def prefixEnd_151292 : Nat := 4983230072969 + 3 ^ 40 * 151292 * 2
def baseEnd_151292 : Nat := 51790343453418202036151

theorem tailTrace_151292 : CollatzResearch.WordTrace tailWord_151292 prefixEnd_151292 51790343453418202036151 := by
  unfold tailWord_151292
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759036283951198730796065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3678715045268264974394753 2759036283951198730796065)
  ·
    refine ⟨2069277212963399048097049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2759036283951198730796065 2069277212963399048097049)
    ·
      refine ⟨1551957909722549286072787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2069277212963399048097049 1551957909722549286072787)
      ·
        refine ⟨2327936864583823929109181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551957909722549286072787 2327936864583823929109181)
        ·
          refine ⟨872976324218933973415943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2327936864583823929109181 872976324218933973415943)
          ·
            refine ⟨1309464486328400960123915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872976324218933973415943 1309464486328400960123915)
            ·
              refine ⟨1964196729492601440185873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309464486328400960123915 1964196729492601440185873)
              ·
                refine ⟨1473147547119451080139405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1964196729492601440185873 1473147547119451080139405)
                ·
                  refine ⟨552430330169794155052277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1473147547119451080139405 552430330169794155052277)
                  ·
                    refine ⟨51790343453418202036151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 552430330169794155052277 51790343453418202036151)
                    ·
                      rfl

theorem cell22_151292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_151292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151292 prefixEnd_151292 := by exact prefixLift 151292
  have htrace : WordTrace (prefixWord ++ tailWord_151292) baseStart_151292 baseEnd_151292 := by
    simpa [prefixWord, tailWord_151292, baseEnd_151292] using wordTrace_append hprefix tailTrace_151292
  have hstable : (prefixWord ++ tailWord_151292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151292).length < 2 ^ (prefixWord ++ tailWord_151292).sum := by decide
  have hdescent : baseEnd_151292 < baseStart_151292 := by decide
  rcases family_descends (prefixWord ++ tailWord_151292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151307 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 4, 4]
def baseStart_151307 : Nat := 118140960795 + 151307 * 2 ^ 59
def prefixEnd_151307 : Nat := 4983230072969 + 3 ^ 40 * 151307 * 2
def baseEnd_151307 : Nat := 51795478259963162911105

theorem tailTrace_151307 : CollatzResearch.WordTrace tailWord_151307 prefixEnd_151307 51795478259963162911105 := by
  unfold tailWord_151307
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518619662848055023388175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3679079775232036682258783 5518619662848055023388175)
  ·
    refine ⟨8277929494272082535082263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5518619662848055023388175 8277929494272082535082263)
    ·
      refine ⟨12416894241408123802623395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8277929494272082535082263 12416894241408123802623395)
      ·
        refine ⟨18625341362112185703935093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12416894241408123802623395 18625341362112185703935093)
        ·
          refine ⟨1746125752698017409743915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18625341362112185703935093 1746125752698017409743915)
          ·
            refine ⟨2619188629047026114615873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746125752698017409743915 2619188629047026114615873)
            ·
              refine ⟨1964391471785269585961905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2619188629047026114615873 1964391471785269585961905)
              ·
                refine ⟨1473293603838952189471429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1964391471785269585961905 1473293603838952189471429)
                ·
                  refine ⟨276242550719803535525893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473293603838952189471429 276242550719803535525893)
                  ·
                    refine ⟨51795478259963162911105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 276242550719803535525893 51795478259963162911105)
                    ·
                      rfl

theorem cell22_151307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_151307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151307 prefixEnd_151307 := by exact prefixLift 151307
  have htrace : WordTrace (prefixWord ++ tailWord_151307) baseStart_151307 baseEnd_151307 := by
    simpa [prefixWord, tailWord_151307, baseEnd_151307] using wordTrace_append hprefix tailTrace_151307
  have hstable : (prefixWord ++ tailWord_151307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151307).length < 2 ^ (prefixWord ++ tailWord_151307).sum := by decide
  have hdescent : baseEnd_151307 < baseStart_151307 := by decide
  rcases family_descends (prefixWord ++ tailWord_151307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151373 : List Nat := [1, 6, 1, 2, 1, 3, 2, 6]
def baseStart_151373 : Nat := 118140960795 + 151373 * 2 ^ 59
def prefixEnd_151373 : Nat := 4983230072969 + 3 ^ 40 * 151373 * 2
def baseEnd_151373 : Nat := 5757563489862332306767

theorem tailTrace_151373 : CollatzResearch.WordTrace tailWord_151373 prefixEnd_151373 5757563489862332306767 := by
  unfold tailWord_151373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521026880608948295290773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3680684587072632196860515 5521026880608948295290773)
  ·
    refine ⟨258798135028544451341755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5521026880608948295290773 258798135028544451341755)
    ·
      refine ⟨388197202542816677012633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258798135028544451341755 388197202542816677012633)
      ·
        refine ⟨291147901907112507759475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388197202542816677012633 291147901907112507759475)
        ·
          refine ⟨436721852860668761639213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291147901907112507759475 436721852860668761639213)
          ·
            refine ⟨163770694822750785614705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 436721852860668761639213 163770694822750785614705)
            ·
              refine ⟨122828021117063089211029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163770694822750785614705 122828021117063089211029)
              ·
                refine ⟨5757563489862332306767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122828021117063089211029 5757563489862332306767)
                ·
                  rfl

theorem cell22_151373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 6].length) (baseStart_151373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151373 prefixEnd_151373 := by exact prefixLift 151373
  have htrace : WordTrace (prefixWord ++ tailWord_151373) baseStart_151373 baseEnd_151373 := by
    simpa [prefixWord, tailWord_151373, baseEnd_151373] using wordTrace_append hprefix tailTrace_151373
  have hstable : (prefixWord ++ tailWord_151373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151373).length < 2 ^ (prefixWord ++ tailWord_151373).sum := by decide
  have hdescent : baseEnd_151373 < baseStart_151373 := by decide
  rcases family_descends (prefixWord ++ tailWord_151373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151431 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 3, 4]
def baseStart_151431 : Nat := 118140960795 + 151431 * 2 ^ 59
def prefixEnd_151431 : Nat := 4983230072969 + 3 ^ 40 * 151431 * 2
def baseEnd_151431 : Nat := 51837925994068172810725

theorem tailTrace_151431 : CollatzResearch.WordTrace tailWord_151431 prefixEnd_151431 51837925994068172810725 := by
  unfold tailWord_151431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5523142314398824200902147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3682094876265882800601431 5523142314398824200902147)
  ·
    refine ⟨8284713471598236301353221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5523142314398824200902147 8284713471598236301353221)
    ·
      refine ⟨1553383775924669306503729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8284713471598236301353221 1553383775924669306503729)
      ·
        refine ⟨1165037831943501979877797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1553383775924669306503729 1165037831943501979877797)
        ·
          refine ⟨218444593489406621227087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1165037831943501979877797 218444593489406621227087)
          ·
            refine ⟨327666890234109931840631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218444593489406621227087 327666890234109931840631)
            ·
              refine ⟨491500335351164897760947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327666890234109931840631 491500335351164897760947)
              ·
                refine ⟨737250503026747346641421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491500335351164897760947 737250503026747346641421)
                ·
                  refine ⟨276468938635030254990533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737250503026747346641421 276468938635030254990533)
                  ·
                    refine ⟨51837925994068172810725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 276468938635030254990533 51837925994068172810725)
                    ·
                      rfl

theorem cell22_151431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_151431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151431 prefixEnd_151431 := by exact prefixLift 151431
  have htrace : WordTrace (prefixWord ++ tailWord_151431) baseStart_151431 baseEnd_151431 := by
    simpa [prefixWord, tailWord_151431, baseEnd_151431] using wordTrace_append hprefix tailTrace_151431
  have hstable : (prefixWord ++ tailWord_151431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151431).length < 2 ^ (prefixWord ++ tailWord_151431).sum := by decide
  have hdescent : baseEnd_151431 < baseStart_151431 := by decide
  rcases family_descends (prefixWord ++ tailWord_151431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151463 : List Nat := [1, 1, 6, 1, 2, 2, 1, 4, 4]
def baseStart_151463 : Nat := 118140960795 + 151463 * 2 ^ 59
def prefixEnd_151463 : Nat := 4983230072969 + 3 ^ 40 * 151463 * 2
def baseEnd_151463 : Nat := 17282960082676918670209

theorem tailTrace_151463 : CollatzResearch.WordTrace tailWord_151463 prefixEnd_151463 17282960082676918670209 := by
  unfold tailWord_151463
  simp only [CollatzResearch.WordTrace]
  refine ⟨5524309450282893666067043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3682872966855262444044695 5524309450282893666067043)
  ·
    refine ⟨8286464175424340499100565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5524309450282893666067043 8286464175424340499100565)
    ·
      refine ⟨388428008223015960895339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8286464175424340499100565 388428008223015960895339)
      ·
        refine ⟨582642012334523941343009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388428008223015960895339 582642012334523941343009)
        ·
          refine ⟨436981509250892956007257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582642012334523941343009 436981509250892956007257)
          ·
            refine ⟨327736131938169717005443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436981509250892956007257 327736131938169717005443)
            ·
              refine ⟨491604197907254575508165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327736131938169717005443 491604197907254575508165)
              ·
                refine ⟨92175787107610232907781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 491604197907254575508165 92175787107610232907781)
                ·
                  refine ⟨17282960082676918670209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92175787107610232907781 17282960082676918670209)
                  ·
                    rfl

theorem cell22_151463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 4].length) (baseStart_151463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151463 prefixEnd_151463 := by exact prefixLift 151463
  have htrace : WordTrace (prefixWord ++ tailWord_151463) baseStart_151463 baseEnd_151463 := by
    simpa [prefixWord, tailWord_151463, baseEnd_151463] using wordTrace_append hprefix tailTrace_151463
  have hstable : (prefixWord ++ tailWord_151463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151463).length < 2 ^ (prefixWord ++ tailWord_151463).sum := by decide
  have hdescent : baseEnd_151463 < baseStart_151463 := by decide
  rcases family_descends (prefixWord ++ tailWord_151463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151523 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 3, 3]
def baseStart_151523 : Nat := 118140960795 + 151523 * 2 ^ 59
def prefixEnd_151523 : Nat := 4983230072969 + 3 ^ 40 * 151523 * 2
def baseEnd_151523 : Nat := 51869419474210599510443

theorem tailTrace_151523 : CollatzResearch.WordTrace tailWord_151523 prefixEnd_151523 51869419474210599510443 := by
  unfold tailWord_151523
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526497830065523913251223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3684331886710349275500815 5526497830065523913251223)
  ·
    refine ⟨8289746745098285869876835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5526497830065523913251223 8289746745098285869876835)
    ·
      refine ⟨12434620117647428804815253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8289746745098285869876835 12434620117647428804815253)
      ·
        refine ⟨582872818014723225225715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12434620117647428804815253 582872818014723225225715)
        ·
          refine ⟨874309227022084837838573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582872818014723225225715 874309227022084837838573)
          ·
            refine ⟨327865960133281814189465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 874309227022084837838573 327865960133281814189465)
            ·
              refine ⟨245899470099961360642099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327865960133281814189465 245899470099961360642099)
              ·
                refine ⟨368849205149942040963149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245899470099961360642099 368849205149942040963149)
                ·
                  refine ⟨138318451931228265361181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368849205149942040963149 138318451931228265361181)
                  ·
                    refine ⟨51869419474210599510443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138318451931228265361181 51869419474210599510443)
                    ·
                      rfl

theorem cell22_151523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 3].length) (baseStart_151523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151523 prefixEnd_151523 := by exact prefixLift 151523
  have htrace : WordTrace (prefixWord ++ tailWord_151523) baseStart_151523 baseEnd_151523 := by
    simpa [prefixWord, tailWord_151523, baseEnd_151523] using wordTrace_append hprefix tailTrace_151523
  have hstable : (prefixWord ++ tailWord_151523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151523).length < 2 ^ (prefixWord ++ tailWord_151523).sum := by decide
  have hdescent : baseEnd_151523 < baseStart_151523 := by decide
  rcases family_descends (prefixWord ++ tailWord_151523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151579 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 5, 5]
def baseStart_151579 : Nat := 118140960795 + 151579 * 2 ^ 59
def prefixEnd_151579 : Nat := 4983230072969 + 3 ^ 40 * 151579 * 2
def baseEnd_151579 : Nat := 51888589418645120110271

theorem tailTrace_151579 : CollatzResearch.WordTrace tailWord_151579 prefixEnd_151579 51888589418645120110271 := by
  unfold tailWord_151579
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528540317862645477289791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3685693545241763651526527 5528540317862645477289791)
  ·
    refine ⟨8292810476793968215934687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528540317862645477289791 8292810476793968215934687)
    ·
      refine ⟨12439215715190952323902031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8292810476793968215934687 12439215715190952323902031)
      ·
        refine ⟨18658823572786428485853047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12439215715190952323902031 18658823572786428485853047)
        ·
          refine ⟨27988235359179642728779571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18658823572786428485853047 27988235359179642728779571)
          ·
            refine ⟨41982353038769464093169357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27988235359179642728779571 41982353038769464093169357)
            ·
              refine ⟨15743382389538549034938509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41982353038769464093169357 15743382389538549034938509)
              ·
                refine ⟨5903768396076955888101941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15743382389538549034938509 5903768396076955888101941)
                ·
                  refine ⟨553478287132214614509557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5903768396076955888101941 553478287132214614509557)
                  ·
                    refine ⟨51888589418645120110271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 553478287132214614509557 51888589418645120110271)
                    ·
                      rfl

theorem cell22_151579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_151579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151579 prefixEnd_151579 := by exact prefixLift 151579
  have htrace : WordTrace (prefixWord ++ tailWord_151579) baseStart_151579 baseEnd_151579 := by
    simpa [prefixWord, tailWord_151579, baseEnd_151579] using wordTrace_append hprefix tailTrace_151579
  have hstable : (prefixWord ++ tailWord_151579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151579).length < 2 ^ (prefixWord ++ tailWord_151579).sum := by decide
  have hdescent : baseEnd_151579 < baseStart_151579 := by decide
  rcases family_descends (prefixWord ++ tailWord_151579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151596 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_151596 : Nat := 118140960795 + 151596 * 2 ^ 59
def prefixEnd_151596 : Nat := 4983230072969 + 3 ^ 40 * 151596 * 2
def baseEnd_151596 : Nat := 51894408866062742435219

theorem tailTrace_151596 : CollatzResearch.WordTrace tailWord_151596 prefixEnd_151596 51894408866062742435219 := by
  unfold tailWord_151596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764580179400528690329321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3686106905867371587105761 2764580179400528690329321)
  ·
    refine ⟨2073435134550396517746991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2764580179400528690329321 2073435134550396517746991)
    ·
      refine ⟨3110152701825594776620487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2073435134550396517746991 3110152701825594776620487)
      ·
        refine ⟨4665229052738392164930731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3110152701825594776620487 4665229052738392164930731)
        ·
          refine ⟨6997843579107588247396097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4665229052738392164930731 6997843579107588247396097)
          ·
            refine ⟨5248382684330691185547073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6997843579107588247396097 5248382684330691185547073)
            ·
              refine ⟨3936287013248018389160305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5248382684330691185547073 3936287013248018389160305)
              ·
                refine ⟨2952215259936013791870229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3936287013248018389160305 2952215259936013791870229)
                ·
                  refine ⟨138385090309500646493917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2952215259936013791870229 138385090309500646493917)
                  ·
                    refine ⟨51894408866062742435219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138385090309500646493917 51894408866062742435219)
                    ·
                      rfl

theorem cell22_151596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_151596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151596 prefixEnd_151596 := by exact prefixLift 151596
  have htrace : WordTrace (prefixWord ++ tailWord_151596) baseStart_151596 baseEnd_151596 := by
    simpa [prefixWord, tailWord_151596, baseEnd_151596] using wordTrace_append hprefix tailTrace_151596
  have hstable : (prefixWord ++ tailWord_151596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151596).length < 2 ^ (prefixWord ++ tailWord_151596).sum := by decide
  have hdescent : baseEnd_151596 < baseStart_151596 := by decide
  rcases family_descends (prefixWord ++ tailWord_151596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151630 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_151630 : Nat := 118140960795 + 151630 * 2 ^ 59
def prefixEnd_151630 : Nat := 4983230072969 + 3 ^ 40 * 151630 * 2
def baseEnd_151630 : Nat := 51906047760897987085115

theorem tailTrace_151630 : CollatzResearch.WordTrace tailWord_151630 prefixEnd_151630 51906047760897987085115 := by
  unfold tailWord_151630
  simp only [CollatzResearch.WordTrace]
  refine ⟨691300055084735148424543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3686933627118587458264229 691300055084735148424543)
  ·
    refine ⟨1036950082627102722636815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691300055084735148424543 1036950082627102722636815)
    ·
      refine ⟨1555425123940654083955223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036950082627102722636815 1555425123940654083955223)
      ·
        refine ⟨2333137685910981125932835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555425123940654083955223 2333137685910981125932835)
        ·
          refine ⟨3499706528866471688899253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333137685910981125932835 3499706528866471688899253)
          ·
            refine ⟨328097487081231720834305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3499706528866471688899253 328097487081231720834305)
            ·
              refine ⟨246073115310923790625729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328097487081231720834305 246073115310923790625729)
              ·
                refine ⟨184554836483192842969297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246073115310923790625729 184554836483192842969297)
                ·
                  refine ⟨138416127362394632226973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184554836483192842969297 138416127362394632226973)
                  ·
                    refine ⟨51906047760897987085115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138416127362394632226973 51906047760897987085115)
                    ·
                      rfl

theorem cell22_151630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_151630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151630 prefixEnd_151630 := by exact prefixLift 151630
  have htrace : WordTrace (prefixWord ++ tailWord_151630) baseStart_151630 baseEnd_151630 := by
    simpa [prefixWord, tailWord_151630, baseEnd_151630] using wordTrace_append hprefix tailTrace_151630
  have hstable : (prefixWord ++ tailWord_151630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151630).length < 2 ^ (prefixWord ++ tailWord_151630).sum := by decide
  have hdescent : baseEnd_151630 < baseStart_151630 := by decide
  rcases family_descends (prefixWord ++ tailWord_151630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151688 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 7]
def baseStart_151688 : Nat := 118140960795 + 151688 * 2 ^ 59
def prefixEnd_151688 : Nat := 4983230072969 + 3 ^ 40 * 151688 * 2
def baseEnd_151688 : Nat := 17308634115401723044979

theorem tailTrace_151688 : CollatzResearch.WordTrace tailWord_151688 prefixEnd_151688 17308634115401723044979 := by
  unfold tailWord_151688
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766257937233878546503859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3688343916311838062005145 2766257937233878546503859)
  ·
    refine ⟨4149386905850817819755789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2766257937233878546503859 4149386905850817819755789)
    ·
      refine ⟨1556020089694056682408421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4149386905850817819755789 1556020089694056682408421)
      ·
        refine ⟨291753766817635627951579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1556020089694056682408421 291753766817635627951579)
        ·
          refine ⟨437630650226453441927369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291753766817635627951579 437630650226453441927369)
          ·
            refine ⟨328222987669840081445527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437630650226453441927369 328222987669840081445527)
            ·
              refine ⟨492334481504760122168291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328222987669840081445527 492334481504760122168291)
              ·
                refine ⟨738501722257140183252437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492334481504760122168291 738501722257140183252437)
                ·
                  refine ⟨17308634115401723044979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 738501722257140183252437 17308634115401723044979)
                  ·
                    rfl

theorem cell22_151688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_151688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151688 prefixEnd_151688 := by exact prefixLift 151688
  have htrace : WordTrace (prefixWord ++ tailWord_151688) baseStart_151688 baseEnd_151688 := by
    simpa [prefixWord, tailWord_151688, baseEnd_151688] using wordTrace_append hprefix tailTrace_151688
  have hstable : (prefixWord ++ tailWord_151688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151688).length < 2 ^ (prefixWord ++ tailWord_151688).sum := by decide
  have hdescent : baseEnd_151688 < baseStart_151688 := by decide
  rcases family_descends (prefixWord ++ tailWord_151688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151731 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 3, 5]
def baseStart_151731 : Nat := 118140960795 + 151731 * 2 ^ 59
def prefixEnd_151731 : Nat := 4983230072969 + 3 ^ 40 * 151731 * 2
def baseEnd_151731 : Nat := 51940622124967390309805

theorem tailTrace_151731 : CollatzResearch.WordTrace tailWord_151731 prefixEnd_151731 51940622124967390309805 := by
  unfold tailWord_151731
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534084213311975436823047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3689389475541316957882031 5534084213311975436823047)
  ·
    refine ⟨8301126319967963155234571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5534084213311975436823047 8301126319967963155234571)
    ·
      refine ⟨12451689479951944732851857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8301126319967963155234571 12451689479951944732851857)
      ·
        refine ⟨9338767109963958549638893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12451689479951944732851857 9338767109963958549638893)
        ·
          refine ⟨3502037666236484456114585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9338767109963958549638893 3502037666236484456114585)
          ·
            refine ⟨2626528249677363342085939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3502037666236484456114585 2626528249677363342085939)
            ·
              refine ⟨3939792374516045013128909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626528249677363342085939 3939792374516045013128909)
              ·
                refine ⟨1477422140443516879923341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3939792374516045013128909 1477422140443516879923341)
                ·
                  refine ⟨554033302666318829971253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1477422140443516879923341 554033302666318829971253)
                  ·
                    refine ⟨51940622124967390309805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 554033302666318829971253 51940622124967390309805)
                    ·
                      rfl

theorem cell22_151731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_151731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151731 prefixEnd_151731 := by exact prefixLift 151731
  have htrace : WordTrace (prefixWord ++ tailWord_151731) baseStart_151731 baseEnd_151731 := by
    simpa [prefixWord, tailWord_151731, baseEnd_151731] using wordTrace_append hprefix tailTrace_151731
  have hstable : (prefixWord ++ tailWord_151731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151731).length < 2 ^ (prefixWord ++ tailWord_151731).sum := by decide
  have hdescent : baseEnd_151731 < baseStart_151731 := by decide
  rcases family_descends (prefixWord ++ tailWord_151731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151761 : List Nat := [1, 2, 2, 1, 2, 2, 3, 9]
def baseStart_151761 : Nat := 118140960795 + 151761 * 2 ^ 59
def prefixEnd_151761 : Nat := 4983230072969 + 3 ^ 40 * 151761 * 2
def baseEnd_151761 : Nat := 5772321304228590228857

theorem tailTrace_151761 : CollatzResearch.WordTrace tailWord_151761 prefixEnd_151761 5772321304228590228857 := by
  unfold tailWord_151761
  simp only [CollatzResearch.WordTrace]
  refine ⟨5535178403203290560415137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3690118935468860373610091 5535178403203290560415137)
  ·
    refine ⟨4151383802402467920311353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5535178403203290560415137 4151383802402467920311353)
    ·
      refine ⟨3113537851801850940233515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4151383802402467920311353 3113537851801850940233515)
      ·
        refine ⟨4670306777702776410350273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113537851801850940233515 4670306777702776410350273)
        ·
          refine ⟨3502730083277082307762705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4670306777702776410350273 3502730083277082307762705)
          ·
            refine ⟨2627047562457811730822029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3502730083277082307762705 2627047562457811730822029)
            ·
              refine ⟨985142835921679399058261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2627047562457811730822029 985142835921679399058261)
              ·
                refine ⟨5772321304228590228857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 985142835921679399058261 5772321304228590228857)
                ·
                  rfl

theorem cell22_151761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 9].length) (baseStart_151761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151761 prefixEnd_151761 := by exact prefixLift 151761
  have htrace : WordTrace (prefixWord ++ tailWord_151761) baseStart_151761 baseEnd_151761 := by
    simpa [prefixWord, tailWord_151761, baseEnd_151761] using wordTrace_append hprefix tailTrace_151761
  have hstable : (prefixWord ++ tailWord_151761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151761).length < 2 ^ (prefixWord ++ tailWord_151761).sum := by decide
  have hdescent : baseEnd_151761 < baseStart_151761 := by decide
  rcases family_descends (prefixWord ++ tailWord_151761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151812 : List Nat := [2, 3, 2, 2, 4, 1, 1, 7]
def baseStart_151812 : Nat := 118140960795 + 151812 * 2 ^ 59
def prefixEnd_151812 : Nat := 4983230072969 + 3 ^ 40 * 151812 * 2
def baseEnd_151812 : Nat := 5774261120034464337173

theorem tailTrace_151812 : CollatzResearch.WordTrace tailWord_151812 prefixEnd_151812 5774261120034464337173 := by
  unfold tailWord_151812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768519263009263135260845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3691359017345684180347793 2768519263009263135260845)
  ·
    refine ⟨1038194723628473675722817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2768519263009263135260845 1038194723628473675722817)
    ·
      refine ⟨778646042721355256792113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1038194723628473675722817 778646042721355256792113)
      ·
        refine ⟨583984532041016442594085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 778646042721355256792113 583984532041016442594085)
        ·
          refine ⟨109497099757690582986391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 583984532041016442594085 109497099757690582986391)
          ·
            refine ⟨164245649636535874479587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109497099757690582986391 164245649636535874479587)
            ·
              refine ⟨246368474454803811719381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164245649636535874479587 246368474454803811719381)
              ·
                refine ⟨5774261120034464337173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 246368474454803811719381 5774261120034464337173)
                ·
                  rfl

theorem cell22_151812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 7].length) (baseStart_151812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151812 prefixEnd_151812 := by exact prefixLift 151812
  have htrace : WordTrace (prefixWord ++ tailWord_151812) baseStart_151812 baseEnd_151812 := by
    simpa [prefixWord, tailWord_151812, baseEnd_151812] using wordTrace_append hprefix tailTrace_151812
  have hstable : (prefixWord ++ tailWord_151812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151812).length < 2 ^ (prefixWord ++ tailWord_151812).sum := by decide
  have hdescent : baseEnd_151812 < baseStart_151812 := by decide
  rcases family_descends (prefixWord ++ tailWord_151812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151844 : List Nat := [2, 3, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_151844 : Nat := 118140960795 + 151844 * 2 ^ 59
def prefixEnd_151844 : Nat := 4983230072969 + 3 ^ 40 * 151844 * 2
def baseEnd_151844 : Nat := 51979304334272762234459

theorem tailTrace_151844 : CollatzResearch.WordTrace tailWord_151844 prefixEnd_151844 51979304334272762234459 := by
  unfold tailWord_151844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769102830951297867843293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3692137107935063823791057 2769102830951297867843293)
  ·
    refine ⟨1038413561606736700441235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2769102830951297867843293 1038413561606736700441235)
    ·
      refine ⟨1557620342410105050661853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038413561606736700441235 1557620342410105050661853)
      ·
        refine ⟨584107628403789393998195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1557620342410105050661853 584107628403789393998195)
        ·
          refine ⟨876161442605684090997293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584107628403789393998195 876161442605684090997293)
          ·
            refine ⟨328560540977131534123985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 876161442605684090997293 328560540977131534123985)
            ·
              refine ⟨246420405732848650592989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328560540977131534123985 246420405732848650592989)
              ·
                refine ⟨92407652149818243972371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246420405732848650592989 92407652149818243972371)
                ·
                  refine ⟨138611478224727365958557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92407652149818243972371 138611478224727365958557)
                  ·
                    refine ⟨51979304334272762234459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138611478224727365958557 51979304334272762234459)
                    ·
                      rfl

theorem cell22_151844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_151844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151844 prefixEnd_151844 := by exact prefixLift 151844
  have htrace : WordTrace (prefixWord ++ tailWord_151844) baseStart_151844 baseEnd_151844 := by
    simpa [prefixWord, tailWord_151844, baseEnd_151844] using wordTrace_append hprefix tailTrace_151844
  have hstable : (prefixWord ++ tailWord_151844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151844).length < 2 ^ (prefixWord ++ tailWord_151844).sum := by decide
  have hdescent : baseEnd_151844 < baseStart_151844 := by decide
  rcases family_descends (prefixWord ++ tailWord_151844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
