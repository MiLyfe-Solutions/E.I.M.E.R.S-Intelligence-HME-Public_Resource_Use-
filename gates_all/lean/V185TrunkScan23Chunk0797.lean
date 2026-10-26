import V185TrunkScan23Chunk0796

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4713271 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 2, 5]
def baseStart_4713271 : Nat := 118140960795 + 4713271 * 2 ^ 59
def prefixEnd_4713271 : Nat := 4983230072969 + 3 ^ 40 * 4713271 * 2
def baseEnd_4713271 : Nat := 806724492632511346412189

theorem tailTrace_4713271 : CollatzResearch.WordTrace tailWord_4713271 prefixEnd_4713271 806724492632511346412189 := by
  unfold tailWord_4713271
  simp only [CollatzResearch.WordTrace]
  refine ⟨171907116107631604445563667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114604744071754402963709111 171907116107631604445563667)
  ·
    refine ⟨257860674161447406668345501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171907116107631604445563667 257860674161447406668345501)
    ·
      refine ⟨96697752810542777500629563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257860674161447406668345501 96697752810542777500629563)
      ·
        refine ⟨145046629215814166250944345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96697752810542777500629563 145046629215814166250944345)
        ·
          refine ⟨108784971911860624688208259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145046629215814166250944345 108784971911860624688208259)
          ·
            refine ⟨163177457867790937032312389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108784971911860624688208259 163177457867790937032312389)
            ·
              refine ⟨30595773350210800693558573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163177457867790937032312389 30595773350210800693558573)
              ·
                refine ⟨11473415006329050260084465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30595773350210800693558573 11473415006329050260084465)
                ·
                  refine ⟨8605061254746787695063349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11473415006329050260084465 8605061254746787695063349)
                  ·
                    refine ⟨806724492632511346412189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8605061254746787695063349 806724492632511346412189)
                    ·
                      rfl

theorem cell23_4713271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_4713271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713271 prefixEnd_4713271 := by exact prefixLift 4713271
  have htrace : WordTrace (prefixWord ++ tailWord_4713271) baseStart_4713271 baseEnd_4713271 := by
    simpa [prefixWord, tailWord_4713271, baseEnd_4713271] using wordTrace_append hprefix tailTrace_4713271
  have hstable : (prefixWord ++ tailWord_4713271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713271).length < 2 ^ (prefixWord ++ tailWord_4713271).sum := by decide
  have hdescent : baseEnd_4713271 < baseStart_4713271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713328 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3]
def baseStart_4713328 : Nat := 118140960795 + 4713328 * 2 ^ 59
def prefixEnd_4713328 : Nat := 4983230072969 + 3 ^ 40 * 4713328 * 2
def baseEnd_4713328 : Nat := 2420202746294840316223805

theorem tailTrace_4713328 : CollatzResearch.WordTrace tailWord_4713328 prefixEnd_4713328 2420202746294840316223805 := by
  unfold tailWord_4713328
  simp only [CollatzResearch.WordTrace]
  refine ⟨85954597534212551590194319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114606130045616735453592425 85954597534212551590194319)
  ·
    refine ⟨128931896301318827385291479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85954597534212551590194319 128931896301318827385291479)
    ·
      refine ⟨193397844451978241077937219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128931896301318827385291479 193397844451978241077937219)
      ·
        refine ⟨290096766677967361616905829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193397844451978241077937219 290096766677967361616905829)
        ·
          refine ⟨54393143752118880303169843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290096766677967361616905829 54393143752118880303169843)
          ·
            refine ⟨81589715628178320454754765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54393143752118880303169843 81589715628178320454754765)
            ·
              refine ⟨30596143360566870170533037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81589715628178320454754765 30596143360566870170533037)
              ·
                refine ⟨11473553760212576313949889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30596143360566870170533037 11473553760212576313949889)
                ·
                  refine ⟨8605165320159432235462417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11473553760212576313949889 8605165320159432235462417)
                  ·
                    refine ⟨6453873990119574176596813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8605165320159432235462417 6453873990119574176596813)
                    ·
                      refine ⟨2420202746294840316223805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6453873990119574176596813 2420202746294840316223805)
                      ·
                        rfl

theorem cell23_4713328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_4713328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713328 prefixEnd_4713328 := by exact prefixLift 4713328
  have htrace : WordTrace (prefixWord ++ tailWord_4713328) baseStart_4713328 baseEnd_4713328 := by
    simpa [prefixWord, tailWord_4713328, baseEnd_4713328] using wordTrace_append hprefix tailTrace_4713328
  have hstable : (prefixWord ++ tailWord_4713328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713328).length < 2 ^ (prefixWord ++ tailWord_4713328).sum := by decide
  have hdescent : baseEnd_4713328 < baseStart_4713328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713352 : List Nat := [2, 1, 3, 3, 2, 2, 1, 4, 1, 4]
def baseStart_4713352 : Nat := 118140960795 + 4713352 * 2 ^ 59
def prefixEnd_4713352 : Nat := 4983230072969 + 3 ^ 40 * 4713352 * 2
def baseEnd_4713352 : Nat := 806738356610182740774565

theorem tailTrace_4713352 : CollatzResearch.WordTrace tailWord_4713352 prefixEnd_4713352 806738356610182740774565 := by
  unfold tailWord_4713352
  simp only [CollatzResearch.WordTrace]
  refine ⟨85955035210169077639631155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114606713613558770186174873 85955035210169077639631155)
  ·
    refine ⟨128932552815253616459446733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85955035210169077639631155 128932552815253616459446733)
    ·
      refine ⟨48349707305720106172292525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128932552815253616459446733 48349707305720106172292525)
      ·
        refine ⟨18131140239645039814609697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48349707305720106172292525 18131140239645039814609697)
        ·
          refine ⟨13598355179733779860957273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18131140239645039814609697 13598355179733779860957273)
          ·
            refine ⟨10198766384800334895717955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13598355179733779860957273 10198766384800334895717955)
            ·
              refine ⟨15298149577200502343576933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10198766384800334895717955 15298149577200502343576933)
              ·
                refine ⟨2868403045725094189420675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15298149577200502343576933 2868403045725094189420675)
                ·
                  refine ⟨4302604568587641284131013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868403045725094189420675 4302604568587641284131013)
                  ·
                    refine ⟨806738356610182740774565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302604568587641284131013 806738356610182740774565)
                    ·
                      rfl

theorem cell23_4713352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_4713352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713352 prefixEnd_4713352 := by exact prefixLift 4713352
  have htrace : WordTrace (prefixWord ++ tailWord_4713352) baseStart_4713352 baseEnd_4713352 := by
    simpa [prefixWord, tailWord_4713352, baseEnd_4713352] using wordTrace_append hprefix tailTrace_4713352
  have hstable : (prefixWord ++ tailWord_4713352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713352).length < 2 ^ (prefixWord ++ tailWord_4713352).sum := by decide
  have hdescent : baseEnd_4713352 < baseStart_4713352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713375 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 3]
def baseStart_4713375 : Nat := 118140960795 + 4713375 * 2 ^ 59
def prefixEnd_4713375 : Nat := 4983230072969 + 3 ^ 40 * 4713375 * 2
def baseEnd_4713375 : Nat := 2420226879885601632336089

theorem tailTrace_4713375 : CollatzResearch.WordTrace tailWord_4713375 prefixEnd_4713375 2420226879885601632336089 := by
  unfold tailWord_4713375
  simp only [CollatzResearch.WordTrace]
  refine ⟨171910909299254830207349579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114607272866169886804899719 171910909299254830207349579)
  ·
    refine ⟨257866363948882245311024369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171910909299254830207349579 257866363948882245311024369)
    ·
      refine ⟨193399772961661683983268277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257866363948882245311024369 193399772961661683983268277)
      ·
        refine ⟨18131228715155782873431401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193399772961661683983268277 18131228715155782873431401)
        ·
          refine ⟨13598421536366837155073551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18131228715155782873431401 13598421536366837155073551)
          ·
            refine ⟨20397632304550255732610327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13598421536366837155073551 20397632304550255732610327)
            ·
              refine ⟨30596448456825383598915491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20397632304550255732610327 30596448456825383598915491)
              ·
                refine ⟨45894672685238075398373237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30596448456825383598915491 45894672685238075398373237)
                ·
                  refine ⟨4302625564241069568597491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45894672685238075398373237 4302625564241069568597491)
                  ·
                    refine ⟨6453938346361604352896237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302625564241069568597491 6453938346361604352896237)
                    ·
                      refine ⟨2420226879885601632336089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6453938346361604352896237 2420226879885601632336089)
                      ·
                        rfl

theorem cell23_4713375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_4713375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713375 prefixEnd_4713375 := by exact prefixLift 4713375
  have htrace : WordTrace (prefixWord ++ tailWord_4713375) baseStart_4713375 baseEnd_4713375 := by
    simpa [prefixWord, tailWord_4713375, baseEnd_4713375] using wordTrace_append hprefix tailTrace_4713375
  have hstable : (prefixWord ++ tailWord_4713375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713375).length < 2 ^ (prefixWord ++ tailWord_4713375).sum := by decide
  have hdescent : baseEnd_4713375 < baseStart_4713375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713391 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 3, 6]
def baseStart_4713391 : Nat := 118140960795 + 4713391 * 2 ^ 59
def prefixEnd_4713391 : Nat := 4983230072969 + 3 ^ 40 * 4713391 * 2
def baseEnd_4713391 : Nat := 806745031858691189912005

theorem tailTrace_4713391 : CollatzResearch.WordTrace tailWord_4713391 prefixEnd_4713391 806745031858691189912005 := by
  unfold tailWord_4713391
  simp only [CollatzResearch.WordTrace]
  refine ⟨171911492867196864939932027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114607661911464576626621351 171911492867196864939932027)
  ·
    refine ⟨257867239300795297409898041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171911492867196864939932027 257867239300795297409898041)
    ·
      refine ⟨193400429475596473057423531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257867239300795297409898041 193400429475596473057423531)
      ·
        refine ⟨290100644213394709586135297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193400429475596473057423531 290100644213394709586135297)
        ·
          refine ⟨217575483160046032189601473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290100644213394709586135297 217575483160046032189601473)
          ·
            refine ⟨163181612370034524142201105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217575483160046032189601473 163181612370034524142201105)
            ·
              refine ⟨122386209277525893106650829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163181612370034524142201105 122386209277525893106650829)
              ·
                refine ⟨45894828479072209914994061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122386209277525893106650829 45894828479072209914994061)
                ·
                  refine ⟨17210560679652078718122773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45894828479072209914994061 17210560679652078718122773)
                  ·
                    refine ⟨806745031858691189912005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17210560679652078718122773 806745031858691189912005)
                    ·
                      rfl

theorem cell23_4713391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_4713391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713391 prefixEnd_4713391 := by exact prefixLift 4713391
  have htrace : WordTrace (prefixWord ++ tailWord_4713391) baseStart_4713391 baseEnd_4713391 := by
    simpa [prefixWord, tailWord_4713391, baseEnd_4713391] using wordTrace_append hprefix tailTrace_4713391
  have hstable : (prefixWord ++ tailWord_4713391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713391).length < 2 ^ (prefixWord ++ tailWord_4713391).sum := by decide
  have hdescent : baseEnd_4713391 < baseStart_4713391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713411 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6]
def baseStart_4713411 : Nat := 118140960795 + 4713411 * 2 ^ 59
def prefixEnd_4713411 : Nat := 4983230072969 + 3 ^ 40 * 4713411 * 2
def baseEnd_4713411 : Nat := 2420245365189163491485923

theorem tailTrace_4713411 : CollatzResearch.WordTrace tailWord_4713411 prefixEnd_4713411 2420245365189163491485923 := by
  unfold tailWord_4713411
  simp only [CollatzResearch.WordTrace]
  refine ⟨171912222327124408355660087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114608148218082938903773391 171912222327124408355660087)
  ·
    refine ⟨257868333490686612533490131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171912222327124408355660087 257868333490686612533490131)
    ·
      refine ⟨386802500236029918800235197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257868333490686612533490131 386802500236029918800235197)
      ·
        refine ⟨145050937588511219550088199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386802500236029918800235197 145050937588511219550088199)
        ·
          refine ⟨217576406382766829325132299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145050937588511219550088199 217576406382766829325132299)
          ·
            refine ⟨326364609574150243987698449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217576406382766829325132299 326364609574150243987698449)
            ·
              refine ⟨244773457180612682990773837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326364609574150243987698449 244773457180612682990773837)
              ·
                refine ⟨91790046442729756121540189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244773457180612682990773837 91790046442729756121540189)
                ·
                  refine ⟨34421267416023658545577571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91790046442729756121540189 34421267416023658545577571)
                  ·
                    refine ⟨51631901124035487818366357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34421267416023658545577571 51631901124035487818366357)
                    ·
                      refine ⟨2420245365189163491485923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51631901124035487818366357 2420245365189163491485923)
                      ·
                        rfl

theorem cell23_4713411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_4713411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713411 prefixEnd_4713411 := by exact prefixLift 4713411
  have htrace : WordTrace (prefixWord ++ tailWord_4713411) baseStart_4713411 baseEnd_4713411 := by
    simpa [prefixWord, tailWord_4713411, baseEnd_4713411] using wordTrace_append hprefix tailTrace_4713411
  have hstable : (prefixWord ++ tailWord_4713411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713411).length < 2 ^ (prefixWord ++ tailWord_4713411).sum := by decide
  have hdescent : baseEnd_4713411 < baseStart_4713411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713432 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 3, 2, 2]
def baseStart_4713432 : Nat := 118140960795 + 4713432 * 2 ^ 59
def prefixEnd_4713432 : Nat := 4983230072969 + 3 ^ 40 * 4713432 * 2
def baseEnd_4713432 : Nat := 2420256148282907909323327

theorem tailTrace_4713432 : CollatzResearch.WordTrace tailWord_4713432 prefixEnd_4713432 2420256148282907909323327 := by
  unfold tailWord_4713432
  simp only [CollatzResearch.WordTrace]
  refine ⟨85956494130024164471087275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114608658840032219294783033 85956494130024164471087275)
  ·
    refine ⟨128934741195036246706630913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85956494130024164471087275 128934741195036246706630913)
    ·
      refine ⟨96701055896277185029973185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128934741195036246706630913 96701055896277185029973185)
      ·
        refine ⟨72525791922207888772479889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96701055896277185029973185 72525791922207888772479889)
        ·
          refine ⟨54394343941655916579359917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72525791922207888772479889 54394343941655916579359917)
          ·
            refine ⟨20397878978120968717259969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54394343941655916579359917 20397878978120968717259969)
            ·
              refine ⟨15298409233590726537944977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20397878978120968717259969 15298409233590726537944977)
              ·
                refine ⟨11473806925193044903458733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15298409233590726537944977 11473806925193044903458733)
                ·
                  refine ⟨4302677596947391838797025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11473806925193044903458733 4302677596947391838797025)
                  ·
                    refine ⟨3227008197710543879097769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4302677596947391838797025 3227008197710543879097769)
                    ·
                      refine ⟨2420256148282907909323327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227008197710543879097769 2420256148282907909323327)
                      ·
                        rfl

theorem cell23_4713432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_4713432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713432 prefixEnd_4713432 := by exact prefixLift 4713432
  have htrace : WordTrace (prefixWord ++ tailWord_4713432) baseStart_4713432 baseEnd_4713432 := by
    simpa [prefixWord, tailWord_4713432, baseEnd_4713432] using wordTrace_append hprefix tailTrace_4713432
  have hstable : (prefixWord ++ tailWord_4713432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713432).length < 2 ^ (prefixWord ++ tailWord_4713432).sum := by decide
  have hdescent : baseEnd_4713432 < baseStart_4713432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713442 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4713442 : Nat := 118140960795 + 4713442 * 2 ^ 59
def prefixEnd_4713442 : Nat := 4983230072969 + 3 ^ 40 * 4713442 * 2
def baseEnd_4713442 : Nat := 806753761029817623399427

theorem tailTrace_4713442 : CollatzResearch.WordTrace tailWord_4713442 prefixEnd_4713442 806753761029817623399427 := by
  unfold tailWord_4713442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42978338247503025162509645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114608901993341400433359053 42978338247503025162509645)
  ·
    refine ⟨16116876842813634435941117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42978338247503025162509645 16116876842813634435941117)
    ·
      refine ⟨6043828816055112913477919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16116876842813634435941117 6043828816055112913477919)
      ·
        refine ⟨9065743224082669370216879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6043828816055112913477919 9065743224082669370216879)
        ·
          refine ⟨13598614836124004055325319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9065743224082669370216879 13598614836124004055325319)
          ·
            refine ⟨20397922254186006082987979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13598614836124004055325319 20397922254186006082987979)
            ·
              refine ⟨30596883381279009124481969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20397922254186006082987979 30596883381279009124481969)
              ·
                refine ⟨22947662535959256843361477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30596883381279009124481969 22947662535959256843361477)
                ·
                  refine ⟨4302686725492360658130277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22947662535959256843361477 4302686725492360658130277)
                  ·
                    refine ⟨806753761029817623399427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302686725492360658130277 806753761029817623399427)
                    ·
                      rfl

theorem cell23_4713442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4713442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713442 prefixEnd_4713442 := by exact prefixLift 4713442
  have htrace : WordTrace (prefixWord ++ tailWord_4713442) baseStart_4713442 baseEnd_4713442 := by
    simpa [prefixWord, tailWord_4713442, baseEnd_4713442] using wordTrace_append hprefix tailTrace_4713442
  have hstable : (prefixWord ++ tailWord_4713442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713442).length < 2 ^ (prefixWord ++ tailWord_4713442).sum := by decide
  have hdescent : baseEnd_4713442 < baseStart_4713442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713451 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 9]
def baseStart_4713451 : Nat := 118140960795 + 4713451 * 2 ^ 59
def prefixEnd_4713451 : Nat := 4983230072969 + 3 ^ 40 * 4713451 * 2
def baseEnd_4713451 : Nat := 806755301471781111661913

theorem tailTrace_4713451 : CollatzResearch.WordTrace tailWord_4713451 prefixEnd_4713451 806755301471781111661913 := by
  unfold tailWord_4713451
  simp only [CollatzResearch.WordTrace]
  refine ⟨171913681246979495187116207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114609120831319663458077471 171913681246979495187116207)
  ·
    refine ⟨257870521870469242780674311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171913681246979495187116207 257870521870469242780674311)
    ·
      refine ⟨386805782805703864171011467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257870521870469242780674311 386805782805703864171011467)
      ·
        refine ⟨580208674208555796256517201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386805782805703864171011467 580208674208555796256517201)
        ·
          refine ⟨435156505656416847192387901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580208674208555796256517201 435156505656416847192387901)
          ·
            refine ⟨163183689621156317697145463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 435156505656416847192387901 163183689621156317697145463)
            ·
              refine ⟨244775534431734476545718195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163183689621156317697145463 244775534431734476545718195)
              ·
                refine ⟨367163301647601714818577293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244775534431734476545718195 367163301647601714818577293)
                ·
                  refine ⟨137686238117850643056966485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367163301647601714818577293 137686238117850643056966485)
                  ·
                    refine ⟨806755301471781111661913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 137686238117850643056966485 806755301471781111661913)
                    ·
                      rfl

theorem cell23_4713451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_4713451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713451 prefixEnd_4713451 := by exact prefixLift 4713451
  have htrace : WordTrace (prefixWord ++ tailWord_4713451) baseStart_4713451 baseEnd_4713451 := by
    simpa [prefixWord, tailWord_4713451, baseEnd_4713451] using wordTrace_append hprefix tailTrace_4713451
  have hstable : (prefixWord ++ tailWord_4713451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713451).length < 2 ^ (prefixWord ++ tailWord_4713451).sum := by decide
  have hdescent : baseEnd_4713451 < baseStart_4713451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713460 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4713460 : Nat := 118140960795 + 4713460 * 2 ^ 59
def prefixEnd_4713460 : Nat := 4983230072969 + 3 ^ 40 * 4713460 * 2
def baseEnd_4713460 : Nat := 2420270525741233799773199

theorem tailTrace_4713460 : CollatzResearch.WordTrace tailWord_4713460 prefixEnd_4713460 2420270525741233799773199 := by
  unfold tailWord_4713460
  simp only [CollatzResearch.WordTrace]
  refine ⟨85957004751973444862096917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114609339669297926482795889 85957004751973444862096917)
  ·
    refine ⟨4029234597748755227910793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85957004751973444862096917 4029234597748755227910793)
    ·
      refine ⟨3021925948311566420933095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4029234597748755227910793 3021925948311566420933095)
      ·
        refine ⟨4532888922467349631399643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021925948311566420933095 4532888922467349631399643)
        ·
          refine ⟨6799333383701024447099465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532888922467349631399643 6799333383701024447099465)
          ·
            refine ⟨5099500037775768335324599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6799333383701024447099465 5099500037775768335324599)
            ·
              refine ⟨7649250056663652502986899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099500037775768335324599 7649250056663652502986899)
              ·
                refine ⟨11473875084995478754480349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7649250056663652502986899 11473875084995478754480349)
                ·
                  refine ⟨4302703156873304532930131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11473875084995478754480349 4302703156873304532930131)
                  ·
                    refine ⟨6454054735309956799395197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302703156873304532930131 6454054735309956799395197)
                    ·
                      refine ⟨2420270525741233799773199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454054735309956799395197 2420270525741233799773199)
                      ·
                        rfl

theorem cell23_4713460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4713460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713460 prefixEnd_4713460 := by exact prefixLift 4713460
  have htrace : WordTrace (prefixWord ++ tailWord_4713460) baseStart_4713460 baseEnd_4713460 := by
    simpa [prefixWord, tailWord_4713460, baseEnd_4713460] using wordTrace_append hprefix tailTrace_4713460
  have hstable : (prefixWord ++ tailWord_4713460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713460).length < 2 ^ (prefixWord ++ tailWord_4713460).sum := by decide
  have hdescent : baseEnd_4713460 < baseStart_4713460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713465 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 3]
def baseStart_4713465 : Nat := 118140960795 + 4713465 * 2 ^ 59
def prefixEnd_4713465 : Nat := 4983230072969 + 3 ^ 40 * 4713465 * 2
def baseEnd_4713465 : Nat := 2420273093144506280210675

theorem tailTrace_4713465 : CollatzResearch.WordTrace tailWord_4713465 prefixEnd_4713465 2420273093144506280210675 := by
  unfold tailWord_4713465
  simp only [CollatzResearch.WordTrace]
  refine ⟨171914191868928775578125849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114609461245952517052083899 171914191868928775578125849)
  ·
    refine ⟨128935643901696581683594387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171914191868928775578125849 128935643901696581683594387)
    ·
      refine ⟨193403465852544872525391581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128935643901696581683594387 193403465852544872525391581)
      ·
        refine ⟨72526299694704327197021843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193403465852544872525391581 72526299694704327197021843)
        ·
          refine ⟨108789449542056490795532765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72526299694704327197021843 108789449542056490795532765)
          ·
            refine ⟨40796043578271184048324787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108789449542056490795532765 40796043578271184048324787)
            ·
              refine ⟨61194065367406776072487181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40796043578271184048324787 61194065367406776072487181)
              ·
                refine ⟨22947774512777541027182693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61194065367406776072487181 22947774512777541027182693)
                ·
                  refine ⟨4302707721145788942596755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22947774512777541027182693 4302707721145788942596755)
                  ·
                    refine ⟨6454061581718683413895133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302707721145788942596755 6454061581718683413895133)
                    ·
                      refine ⟨2420273093144506280210675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454061581718683413895133 2420273093144506280210675)
                      ·
                        rfl

theorem cell23_4713465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_4713465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713465 prefixEnd_4713465 := by exact prefixLift 4713465
  have htrace : WordTrace (prefixWord ++ tailWord_4713465) baseStart_4713465 baseEnd_4713465 := by
    simpa [prefixWord, tailWord_4713465, baseEnd_4713465] using wordTrace_append hprefix tailTrace_4713465
  have hstable : (prefixWord ++ tailWord_4713465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713465).length < 2 ^ (prefixWord ++ tailWord_4713465).sum := by decide
  have hdescent : baseEnd_4713465 < baseStart_4713465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713509 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 1, 3, 2]
def baseStart_4713509 : Nat := 118140960795 + 4713509 * 2 ^ 59
def prefixEnd_4713509 : Nat := 4983230072969 + 3 ^ 40 * 4713509 * 2
def baseEnd_4713509 : Nat := 2420295686293304108060473

theorem tailTrace_4713509 : CollatzResearch.WordTrace tailWord_4713509 prefixEnd_4713509 2420295686293304108060473 := by
  unfold tailWord_4713509
  simp only [CollatzResearch.WordTrace]
  refine ⟨171915796680769371092727581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114610531120512914061818387 171915796680769371092727581)
  ·
    refine ⟨64468423755288514159772843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171915796680769371092727581 64468423755288514159772843)
    ·
      refine ⟨96702635632932771239659265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64468423755288514159772843 96702635632932771239659265)
      ·
        refine ⟨72526976724699578429744449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96702635632932771239659265 72526976724699578429744449)
        ·
          refine ⟨54395232543524683822308337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72526976724699578429744449 54395232543524683822308337)
          ·
            refine ⟨40796424407643512866731253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54395232543524683822308337 40796424407643512866731253)
            ·
              refine ⟨3824664788216579331256055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40796424407643512866731253 3824664788216579331256055)
              ·
                refine ⟨5736997182324868996884083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824664788216579331256055 5736997182324868996884083)
                ·
                  refine ⟨8605495773487303495326125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736997182324868996884083 8605495773487303495326125)
                  ·
                    refine ⟨3227060915057738810747297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8605495773487303495326125 3227060915057738810747297)
                    ·
                      refine ⟨2420295686293304108060473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227060915057738810747297 2420295686293304108060473)
                      ·
                        rfl

theorem cell23_4713509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_4713509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713509 prefixEnd_4713509 := by exact prefixLift 4713509
  have htrace : WordTrace (prefixWord ++ tailWord_4713509) baseStart_4713509 baseEnd_4713509 := by
    simpa [prefixWord, tailWord_4713509, baseEnd_4713509] using wordTrace_append hprefix tailTrace_4713509
  have hstable : (prefixWord ++ tailWord_4713509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713509).length < 2 ^ (prefixWord ++ tailWord_4713509).sum := by decide
  have hdescent : baseEnd_4713509 < baseStart_4713509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713632 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3]
def baseStart_4713632 : Nat := 118140960795 + 4713632 * 2 ^ 59
def prefixEnd_4713632 : Nat := 4983230072969 + 3 ^ 40 * 4713632 * 2
def baseEnd_4713632 : Nat := 2420358844413807126822407

theorem tailTrace_4713632 : CollatzResearch.WordTrace tailWord_4713632 prefixEnd_4713632 2420358844413807126822407 := by
  unfold tailWord_4713632
  simp only [CollatzResearch.WordTrace]
  refine ⟨85960141429661881549727575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114613521906215842066303433 85960141429661881549727575)
  ·
    refine ⟨128940212144492822324591363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85960141429661881549727575 128940212144492822324591363)
    ·
      refine ⟨193410318216739233486887045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128940212144492822324591363 193410318216739233486887045)
      ·
        refine ⟨36264434665638606278791321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193410318216739233486887045 36264434665638606278791321)
        ·
          refine ⟨27198325999228954709093491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36264434665638606278791321 27198325999228954709093491)
          ·
            refine ⟨40797488998843432063640237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27198325999228954709093491 40797488998843432063640237)
            ·
              refine ⟨15299058374566287023865089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40797488998843432063640237 15299058374566287023865089)
              ·
                refine ⟨11474293780924715267898817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15299058374566287023865089 11474293780924715267898817)
                ·
                  refine ⟨8605720335693536450924113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11474293780924715267898817 8605720335693536450924113)
                  ·
                    refine ⟨6454290251770152338193085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8605720335693536450924113 6454290251770152338193085)
                    ·
                      refine ⟨2420358844413807126822407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454290251770152338193085 2420358844413807126822407)
                      ·
                        rfl

theorem cell23_4713632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_4713632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713632 prefixEnd_4713632 := by exact prefixLift 4713632
  have htrace : WordTrace (prefixWord ++ tailWord_4713632) baseStart_4713632 baseEnd_4713632 := by
    simpa [prefixWord, tailWord_4713632, baseEnd_4713632] using wordTrace_append hprefix tailTrace_4713632
  have hstable : (prefixWord ++ tailWord_4713632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713632).length < 2 ^ (prefixWord ++ tailWord_4713632).sum := by decide
  have hdescent : baseEnd_4713632 < baseStart_4713632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713639 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 3, 4]
def baseStart_4713639 : Nat := 118140960795 + 4713639 * 2 ^ 59
def prefixEnd_4713639 : Nat := 4983230072969 + 3 ^ 40 * 4713639 * 2
def baseEnd_4713639 : Nat := 806787479592796199811625

theorem tailTrace_4713639 : CollatzResearch.WordTrace tailWord_4713639 prefixEnd_4713639 806787479592796199811625 := by
  unfold tailWord_4713639
  simp only [CollatzResearch.WordTrace]
  refine ⟨171920538170298403294959971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114613692113532268863306647 171920538170298403294959971)
  ·
    refine ⟨257880807255447604942439957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171920538170298403294959971 257880807255447604942439957)
    ·
      refine ⟨12088162840099106481676873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 257880807255447604942439957 12088162840099106481676873)
      ·
        refine ⟨9066122130074329861257655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12088162840099106481676873 9066122130074329861257655)
        ·
          refine ⟨13599183195111494791886483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9066122130074329861257655 13599183195111494791886483)
          ·
            refine ⟨20398774792667242187829725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13599183195111494791886483 20398774792667242187829725)
            ·
              refine ⟨7649540547250215820436147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20398774792667242187829725 7649540547250215820436147)
              ·
                refine ⟨11474310820875323730654221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7649540547250215820436147 11474310820875323730654221)
                ·
                  refine ⟨4302866557828246398995333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11474310820875323730654221 4302866557828246398995333)
                  ·
                    refine ⟨806787479592796199811625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302866557828246398995333 806787479592796199811625)
                    ·
                      rfl

theorem cell23_4713639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_4713639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713639 prefixEnd_4713639 := by exact prefixLift 4713639
  have htrace : WordTrace (prefixWord ++ tailWord_4713639) baseStart_4713639 baseEnd_4713639 := by
    simpa [prefixWord, tailWord_4713639, baseEnd_4713639] using wordTrace_append hprefix tailTrace_4713639
  have hstable : (prefixWord ++ tailWord_4713639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713639).length < 2 ^ (prefixWord ++ tailWord_4713639).sum := by decide
  have hdescent : baseEnd_4713639 < baseStart_4713639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713672 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_4713672 : Nat := 118140960795 + 4713672 * 2 ^ 59
def prefixEnd_4713672 : Nat := 4983230072969 + 3 ^ 40 * 4713672 * 2
def baseEnd_4713672 : Nat := 2420379383639986970322223

theorem tailTrace_4713672 : CollatzResearch.WordTrace tailWord_4713672 prefixEnd_4713672 2420379383639986970322223 := by
  unfold tailWord_4713672
  simp only [CollatzResearch.WordTrace]
  refine ⟨85960870889589424965455635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114614494519452566620607513 85960870889589424965455635)
  ·
    refine ⟨128941306334384137448183453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85960870889589424965455635 128941306334384137448183453)
    ·
      refine ⟨48352989875394051543068795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128941306334384137448183453 48352989875394051543068795)
      ·
        refine ⟨72529484813091077314603193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48352989875394051543068795 72529484813091077314603193)
        ·
          refine ⟨54397113609818307985952395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72529484813091077314603193 54397113609818307985952395)
          ·
            refine ⟨81595670414727461978928593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54397113609818307985952395 81595670414727461978928593)
            ·
              refine ⟨61196752811045596484196445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81595670414727461978928593 61196752811045596484196445)
              ·
                refine ⟨22948782304142098681573667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61196752811045596484196445 22948782304142098681573667)
                ·
                  refine ⟨34423173456213148022360501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22948782304142098681573667 34423173456213148022360501)
                  ·
                    refine ⟨3227172511519982627096297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34423173456213148022360501 3227172511519982627096297)
                    ·
                      refine ⟨2420379383639986970322223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227172511519982627096297 2420379383639986970322223)
                      ·
                        rfl

theorem cell23_4713672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_4713672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713672 prefixEnd_4713672 := by exact prefixLift 4713672
  have htrace : WordTrace (prefixWord ++ tailWord_4713672) baseStart_4713672 baseEnd_4713672 := by
    simpa [prefixWord, tailWord_4713672, baseEnd_4713672] using wordTrace_append hprefix tailTrace_4713672
  have hstable : (prefixWord ++ tailWord_4713672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713672).length < 2 ^ (prefixWord ++ tailWord_4713672).sum := by decide
  have hdescent : baseEnd_4713672 < baseStart_4713672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713686 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_4713686 : Nat := 118140960795 + 4713686 * 2 ^ 59
def prefixEnd_4713686 : Nat := 4983230072969 + 3 ^ 40 * 4713686 * 2
def baseEnd_4713686 : Nat := 268931841374349990616351

theorem tailTrace_4713686 : CollatzResearch.WordTrace tailWord_4713686 prefixEnd_4713686 268931841374349990616351 := by
  unfold tailWord_4713686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10745140775070508145120057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114614834934085420214613941 10745140775070508145120057)
  ·
    refine ⟨8058855581302881108840043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10745140775070508145120057 8058855581302881108840043)
    ·
      refine ⟨12088283371954321663260065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8058855581302881108840043 12088283371954321663260065)
      ·
        refine ⟨9066212528965741247445049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12088283371954321663260065 9066212528965741247445049)
        ·
          refine ⟨6799659396724305935583787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9066212528965741247445049 6799659396724305935583787)
          ·
            refine ⟨10199489095086458903375681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6799659396724305935583787 10199489095086458903375681)
            ·
              refine ⟨7649616821314844177531761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10199489095086458903375681 7649616821314844177531761)
              ·
                refine ⟨5737212615986133133148821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7649616821314844177531761 5737212615986133133148821)
                ·
                  refine ⟨268931841374349990616351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5737212615986133133148821 268931841374349990616351)
                  ·
                    rfl

theorem cell23_4713686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_4713686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713686 prefixEnd_4713686 := by exact prefixLift 4713686
  have htrace : WordTrace (prefixWord ++ tailWord_4713686) baseStart_4713686 baseEnd_4713686 := by
    simpa [prefixWord, tailWord_4713686, baseEnd_4713686] using wordTrace_append hprefix tailTrace_4713686
  have hstable : (prefixWord ++ tailWord_4713686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713686).length < 2 ^ (prefixWord ++ tailWord_4713686).sum := by decide
  have hdescent : baseEnd_4713686 < baseStart_4713686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713696 : List Nat := [2, 1, 1, 3, 1, 5, 1, 4, 1, 1, 3]
def baseStart_4713696 : Nat := 118140960795 + 4713696 * 2 ^ 59
def prefixEnd_4713696 : Nat := 4983230072969 + 3 ^ 40 * 4713696 * 2
def baseEnd_4713696 : Nat := 2420391707175694876422113

theorem tailTrace_4713696 : CollatzResearch.WordTrace tailWord_4713696 prefixEnd_4713696 2420391707175694876422113 := by
  unfold tailWord_4713696
  simp only [CollatzResearch.WordTrace]
  refine ⟨85961308565545951014892471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114615078087394601353189961 85961308565545951014892471)
  ·
    refine ⟨128941962848318926522338707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85961308565545951014892471 128941962848318926522338707)
    ·
      refine ⟨193412944272478389783508061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128941962848318926522338707 193412944272478389783508061)
      ·
        refine ⟨72529854102179396168815523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193412944272478389783508061 72529854102179396168815523)
        ·
          refine ⟨108794781153269094253223285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72529854102179396168815523 108794781153269094253223285)
          ·
            refine ⟨10199510733118977586239683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108794781153269094253223285 10199510733118977586239683)
            ·
              refine ⟨15299266099678466379359525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10199510733118977586239683 15299266099678466379359525)
              ·
                refine ⟨2868612393689712446129911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15299266099678466379359525 2868612393689712446129911)
                ·
                  refine ⟨4302918590534568669194867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868612393689712446129911 4302918590534568669194867)
                  ·
                    refine ⟨6454377885801853003792301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302918590534568669194867 6454377885801853003792301)
                    ·
                      refine ⟨2420391707175694876422113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454377885801853003792301 2420391707175694876422113)
                      ·
                        rfl

theorem cell23_4713696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_4713696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713696 prefixEnd_4713696 := by exact prefixLift 4713696
  have htrace : WordTrace (prefixWord ++ tailWord_4713696) baseStart_4713696 baseEnd_4713696 := by
    simpa [prefixWord, tailWord_4713696, baseEnd_4713696] using wordTrace_append hprefix tailTrace_4713696
  have hstable : (prefixWord ++ tailWord_4713696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713696).length < 2 ^ (prefixWord ++ tailWord_4713696).sum := by decide
  have hdescent : baseEnd_4713696 < baseStart_4713696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713705 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 3]
def baseStart_4713705 : Nat := 118140960795 + 4713705 * 2 ^ 59
def prefixEnd_4713705 : Nat := 4983230072969 + 3 ^ 40 * 4713705 * 2
def baseEnd_4713705 : Nat := 2420396328501585341209571

theorem tailTrace_4713705 : CollatzResearch.WordTrace tailWord_4713705 prefixEnd_4713705 2420396328501585341209571 := by
  unfold tailWord_4713705
  simp only [CollatzResearch.WordTrace]
  refine ⟨171922945388059296566862569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114615296925372864377908379 171922945388059296566862569)
  ·
    refine ⟨128942209041044472425146927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171922945388059296566862569 128942209041044472425146927)
    ·
      refine ⟨193413313561566708637720391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128942209041044472425146927 193413313561566708637720391)
      ·
        refine ⟨290119970342350062956580587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193413313561566708637720391 290119970342350062956580587)
        ·
          refine ⟨435179955513525094434870881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290119970342350062956580587 435179955513525094434870881)
          ·
            refine ⟨326384966635143820826153161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435179955513525094434870881 326384966635143820826153161)
            ·
              refine ⟨244788724976357865619614871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326384966635143820826153161 244788724976357865619614871)
              ·
                refine ⟨367183087464536798429422307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244788724976357865619614871 367183087464536798429422307)
                ·
                  refine ⟨550774631196805197644133461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367183087464536798429422307 550774631196805197644133461)
                  ·
                    refine ⟨6454390209337560909892189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 550774631196805197644133461 6454390209337560909892189)
                    ·
                      refine ⟨2420396328501585341209571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454390209337560909892189 2420396328501585341209571)
                      ·
                        rfl

theorem cell23_4713705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_4713705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713705 prefixEnd_4713705 := by exact prefixLift 4713705
  have htrace : WordTrace (prefixWord ++ tailWord_4713705) baseStart_4713705 baseEnd_4713705 := by
    simpa [prefixWord, tailWord_4713705, baseEnd_4713705] using wordTrace_append hprefix tailTrace_4713705
  have hstable : (prefixWord ++ tailWord_4713705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713705).length < 2 ^ (prefixWord ++ tailWord_4713705).sum := by decide
  have hdescent : baseEnd_4713705 < baseStart_4713705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713719 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 3, 2, 2]
def baseStart_4713719 : Nat := 118140960795 + 4713719 * 2 ^ 59
def prefixEnd_4713719 : Nat := 4983230072969 + 3 ^ 40 * 4713719 * 2
def baseEnd_4713719 : Nat := 2420403517230748286434507

theorem tailTrace_4713719 : CollatzResearch.WordTrace tailWord_4713719 prefixEnd_4713719 2420403517230748286434507 := by
  unfold tailWord_4713719
  simp only [CollatzResearch.WordTrace]
  refine ⟨171923456010008576957872211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114615637340005717971914807 171923456010008576957872211)
  ·
    refine ⟨257885184015012865436808317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171923456010008576957872211 257885184015012865436808317)
    ·
      refine ⟨96706944005629824538803119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257885184015012865436808317 96706944005629824538803119)
      ·
        refine ⟨145060416008444736808204679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96706944005629824538803119 145060416008444736808204679)
        ·
          refine ⟨217590624012667105212307019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145060416008444736808204679 217590624012667105212307019)
          ·
            refine ⟨326385936019000657818460529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217590624012667105212307019 326385936019000657818460529)
            ·
              refine ⟨244789452014250493363845397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326385936019000657818460529 244789452014250493363845397)
              ·
                refine ⟨11474505563167991876430253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 244789452014250493363845397 11474505563167991876430253)
                ·
                  refine ⟨4302939586187996953661345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11474505563167991876430253 4302939586187996953661345)
                  ·
                    refine ⟨3227204689640997715246009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4302939586187996953661345 3227204689640997715246009)
                    ·
                      refine ⟨2420403517230748286434507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227204689640997715246009 2420403517230748286434507)
                      ·
                        rfl

theorem cell23_4713719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_4713719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713719 prefixEnd_4713719 := by exact prefixLift 4713719
  have htrace : WordTrace (prefixWord ++ tailWord_4713719) baseStart_4713719 baseEnd_4713719 := by
    simpa [prefixWord, tailWord_4713719, baseEnd_4713719] using wordTrace_append hprefix tailTrace_4713719
  have hstable : (prefixWord ++ tailWord_4713719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713719).length < 2 ^ (prefixWord ++ tailWord_4713719).sum := by decide
  have hdescent : baseEnd_4713719 < baseStart_4713719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713722 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_4713722 : Nat := 118140960795 + 4713722 * 2 ^ 59
def prefixEnd_4713722 : Nat := 4983230072969 + 3 ^ 40 * 4713722 * 2
def baseEnd_4713722 : Nat := 2420405057672711774696993

theorem tailTrace_4713722 : CollatzResearch.WordTrace tailWord_4713722 prefixEnd_4713722 2420405057672711774696993 := by
  unfold tailWord_4713722
  simp only [CollatzResearch.WordTrace]
  refine ⟨42980891357249427117557855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114615710285998472313487613 42980891357249427117557855)
  ·
    refine ⟨64471337035874140676336783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42980891357249427117557855 64471337035874140676336783)
    ·
      refine ⟨96707005553811211014505175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64471337035874140676336783 96707005553811211014505175)
      ·
        refine ⟨145060508330716816521757763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96707005553811211014505175 145060508330716816521757763)
        ·
          refine ⟨217590762496075224782636645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145060508330716816521757763 217590762496075224782636645)
          ·
            refine ⟨40798267968014104646744371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217590762496075224782636645 40798267968014104646744371)
            ·
              refine ⟨61197401952021156970116557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40798267968014104646744371 61197401952021156970116557)
              ·
                refine ⟨22949025732007933863793709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61197401952021156970116557 22949025732007933863793709)
                ·
                  refine ⟨8605884649502975198922641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22949025732007933863793709 8605884649502975198922641)
                  ·
                    refine ⟨6454413487127231399191981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8605884649502975198922641 6454413487127231399191981)
                    ·
                      refine ⟨2420405057672711774696993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454413487127231399191981 2420405057672711774696993)
                      ·
                        rfl

theorem cell23_4713722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_4713722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713722 prefixEnd_4713722 := by exact prefixLift 4713722
  have htrace : WordTrace (prefixWord ++ tailWord_4713722) baseStart_4713722 baseEnd_4713722 := by
    simpa [prefixWord, tailWord_4713722, baseEnd_4713722] using wordTrace_append hprefix tailTrace_4713722
  have hstable : (prefixWord ++ tailWord_4713722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713722).length < 2 ^ (prefixWord ++ tailWord_4713722).sum := by decide
  have hdescent : baseEnd_4713722 < baseStart_4713722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713730 : List Nat := [3, 4, 1, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_4713730 : Nat := 118140960795 + 4713730 * 2 ^ 59
def prefixEnd_4713730 : Nat := 4983230072969 + 3 ^ 40 * 4713730 * 2
def baseEnd_4713730 : Nat := 2420409165517947743396957

theorem tailTrace_4713730 : CollatzResearch.WordTrace tailWord_4713730 prefixEnd_4713730 2420409165517947743396957 := by
  unfold tailWord_4713730
  simp only [CollatzResearch.WordTrace]
  refine ⟨42980964303242181459130661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114615904808645817224348429 42980964303242181459130661)
  ·
    refine ⟨8058930806857909023586999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42980964303242181459130661 8058930806857909023586999)
    ·
      refine ⟨12088396210286863535380499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8058930806857909023586999 12088396210286863535380499)
      ·
        refine ⟨18132594315430295303070749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12088396210286863535380499 18132594315430295303070749)
        ·
          refine ⟨6799722868286360738651531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18132594315430295303070749 6799722868286360738651531)
          ·
            refine ⟨10199584302429541107977297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6799722868286360738651531 10199584302429541107977297)
            ·
              refine ⟨7649688226822155830982973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10199584302429541107977297 7649688226822155830982973)
              ·
                refine ⟨2868633085058308436618615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7649688226822155830982973 2868633085058308436618615)
                ·
                  refine ⟨4302949627587462654927923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868633085058308436618615 4302949627587462654927923)
                  ·
                    refine ⟨6454424441381193982391885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302949627587462654927923 6454424441381193982391885)
                    ·
                      refine ⟨2420409165517947743396957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454424441381193982391885 2420409165517947743396957)
                      ·
                        rfl

theorem cell23_4713730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_4713730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713730 prefixEnd_4713730 := by exact prefixLift 4713730
  have htrace : WordTrace (prefixWord ++ tailWord_4713730) baseStart_4713730 baseEnd_4713730 := by
    simpa [prefixWord, tailWord_4713730, baseEnd_4713730] using wordTrace_append hprefix tailTrace_4713730
  have hstable : (prefixWord ++ tailWord_4713730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713730).length < 2 ^ (prefixWord ++ tailWord_4713730).sum := by decide
  have hdescent : baseEnd_4713730 < baseStart_4713730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713739 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 3]
def baseStart_4713739 : Nat := 118140960795 + 4713739 * 2 ^ 59
def prefixEnd_4713739 : Nat := 4983230072969 + 3 ^ 40 * 4713739 * 2
def baseEnd_4713739 : Nat := 2420413786843838208184415

theorem tailTrace_4713739 : CollatzResearch.WordTrace tailWord_4713739 prefixEnd_4713739 2420413786843838208184415 := by
  unfold tailWord_4713739
  simp only [CollatzResearch.WordTrace]
  refine ⟨171924185469936120373600271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114616123646624080249066847 171924185469936120373600271)
  ·
    refine ⟨257886278204904180560400407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171924185469936120373600271 257886278204904180560400407)
    ·
      refine ⟨386829417307356270840600611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257886278204904180560400407 386829417307356270840600611)
      ·
        refine ⟨580244125961034406260900917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386829417307356270840600611 580244125961034406260900917)
        ·
          refine ⟨54397886808846975586959461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 580244125961034406260900917 54397886808846975586959461)
          ·
            refine ⟨10199603776658807922554899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54397886808846975586959461 10199603776658807922554899)
            ·
              refine ⟨15299405664988211883832349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10199603776658807922554899 15299405664988211883832349)
              ·
                refine ⟨5737277124370579456437131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15299405664988211883832349 5737277124370579456437131)
                ·
                  refine ⟨8605915686555869184655697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5737277124370579456437131 8605915686555869184655697)
                  ·
                    refine ⟨6454436764916901888491773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8605915686555869184655697 6454436764916901888491773)
                    ·
                      refine ⟨2420413786843838208184415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454436764916901888491773 2420413786843838208184415)
                      ·
                        rfl

theorem cell23_4713739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 3].length) (baseStart_4713739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713739 prefixEnd_4713739 := by exact prefixLift 4713739
  have htrace : WordTrace (prefixWord ++ tailWord_4713739) baseStart_4713739 baseEnd_4713739 := by
    simpa [prefixWord, tailWord_4713739, baseEnd_4713739] using wordTrace_append hprefix tailTrace_4713739
  have hstable : (prefixWord ++ tailWord_4713739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713739).length < 2 ^ (prefixWord ++ tailWord_4713739).sum := by decide
  have hdescent : baseEnd_4713739 < baseStart_4713739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713773 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_4713773 : Nat := 118140960795 + 4713773 * 2 ^ 59
def prefixEnd_4713773 : Nat := 4983230072969 + 3 ^ 40 * 4713773 * 2
def baseEnd_4713773 : Nat := 2420431245186091075159259

theorem tailTrace_4713773 : CollatzResearch.WordTrace tailWord_4713773 prefixEnd_4713773 2420431245186091075159259 := by
  unfold tailWord_4713773
  simp only [CollatzResearch.WordTrace]
  refine ⟨171925425551812944180337973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114616950367875296120225315 171925425551812944180337973)
  ·
    refine ⟨16118008645482463516906685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171925425551812944180337973 16118008645482463516906685)
    ·
      refine ⟨6044253242055923818840007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16118008645482463516906685 6044253242055923818840007)
      ·
        refine ⟨9066379863083885728260011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6044253242055923818840007 9066379863083885728260011)
        ·
          refine ⟨13599569794625828592390017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9066379863083885728260011 13599569794625828592390017)
          ·
            refine ⟨10199677345969371444292513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13599569794625828592390017 10199677345969371444292513)
            ·
              refine ⟨7649758009477028583219385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10199677345969371444292513 7649758009477028583219385)
              ·
                refine ⟨5737318507107771437414539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7649758009477028583219385 5737318507107771437414539)
                ·
                  refine ⟨8605977760661657156121809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5737318507107771437414539 8605977760661657156121809)
                  ·
                    refine ⟨6454483320496242867091357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8605977760661657156121809 6454483320496242867091357)
                    ·
                      refine ⟨2420431245186091075159259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454483320496242867091357 2420431245186091075159259)
                      ·
                        rfl

theorem cell23_4713773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_4713773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713773 prefixEnd_4713773 := by exact prefixLift 4713773
  have htrace : WordTrace (prefixWord ++ tailWord_4713773) baseStart_4713773 baseEnd_4713773 := by
    simpa [prefixWord, tailWord_4713773, baseEnd_4713773] using wordTrace_append hprefix tailTrace_4713773
  have hstable : (prefixWord ++ tailWord_4713773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713773).length < 2 ^ (prefixWord ++ tailWord_4713773).sum := by decide
  have hdescent : baseEnd_4713773 < baseStart_4713773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713812 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_4713812 : Nat := 118140960795 + 4713812 * 2 ^ 59
def prefixEnd_4713812 : Nat := 4983230072969 + 3 ^ 40 * 4713812 * 2
def baseEnd_4713812 : Nat := 2420451270931616422571579

theorem tailTrace_4713812 : CollatzResearch.WordTrace tailWord_4713812 prefixEnd_4713812 2420451270931616422571579 := by
  unfold tailWord_4713812
  simp only [CollatzResearch.WordTrace]
  refine ⟨85963423999335826920503845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114617898665781102560671793 85963423999335826920503845)
  ·
    refine ⟨16118141999875467547594471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85963423999335826920503845 16118141999875467547594471)
    ·
      refine ⟨24177212999813201321391707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16118141999875467547594471 24177212999813201321391707)
      ·
        refine ⟨36265819499719801982087561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24177212999813201321391707 36265819499719801982087561)
        ·
          refine ⟨27199364624789851486565671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36265819499719801982087561 27199364624789851486565671)
          ·
            refine ⟨40799046937184777229848507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27199364624789851486565671 40799046937184777229848507)
            ·
              refine ⟨61198570405777165844772761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40799046937184777229848507 61198570405777165844772761)
              ·
                refine ⟨45898927804332874383579571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61198570405777165844772761 45898927804332874383579571)
                ·
                  refine ⟨68848391706499311575369357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45898927804332874383579571 68848391706499311575369357)
                  ·
                    refine ⟨25818146889937241840763509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68848391706499311575369357 25818146889937241840763509)
                    ·
                      refine ⟨2420451270931616422571579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25818146889937241840763509 2420451270931616422571579)
                      ·
                        rfl

theorem cell23_4713812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_4713812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713812 prefixEnd_4713812 := by exact prefixLift 4713812
  have htrace : WordTrace (prefixWord ++ tailWord_4713812) baseStart_4713812 baseEnd_4713812 := by
    simpa [prefixWord, tailWord_4713812, baseEnd_4713812] using wordTrace_append hprefix tailTrace_4713812
  have hstable : (prefixWord ++ tailWord_4713812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713812).length < 2 ^ (prefixWord ++ tailWord_4713812).sum := by decide
  have hdescent : baseEnd_4713812 < baseStart_4713812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713814 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4713814 : Nat := 118140960795 + 4713814 * 2 ^ 59
def prefixEnd_4713814 : Nat := 4983230072969 + 3 ^ 40 * 4713814 * 2
def baseEnd_4713814 : Nat := 806817432630975138248857

theorem tailTrace_4713814 : CollatzResearch.WordTrace tailWord_4713814 prefixEnd_4713814 806817432630975138248857 := by
  unfold tailWord_4713814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10745432559041525511411281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114617947296442938788386997 10745432559041525511411281)
  ·
    refine ⟨8059074419281144133558461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10745432559041525511411281 8059074419281144133558461)
    ·
      refine ⟨3022152907230429050084423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8059074419281144133558461 3022152907230429050084423)
      ·
        refine ⟨4533229360845643575126635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3022152907230429050084423 4533229360845643575126635)
        ·
          refine ⟨6799844041268465362689953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4533229360845643575126635 6799844041268465362689953)
          ·
            refine ⟨5099883030951349022017465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6799844041268465362689953 5099883030951349022017465)
            ·
              refine ⟨3824912273213511766513099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5099883030951349022017465 3824912273213511766513099)
              ·
                refine ⟨5737368409820267649769649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824912273213511766513099 5737368409820267649769649)
                ·
                  refine ⟨4303026307365200737327237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5737368409820267649769649 4303026307365200737327237)
                  ·
                    refine ⟨806817432630975138248857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4303026307365200737327237 806817432630975138248857)
                    ·
                      rfl

theorem cell23_4713814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4713814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713814 prefixEnd_4713814 := by exact prefixLift 4713814
  have htrace : WordTrace (prefixWord ++ tailWord_4713814) baseStart_4713814 baseEnd_4713814 := by
    simpa [prefixWord, tailWord_4713814, baseEnd_4713814] using wordTrace_append hprefix tailTrace_4713814
  have hstable : (prefixWord ++ tailWord_4713814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713814).length < 2 ^ (prefixWord ++ tailWord_4713814).sum := by decide
  have hdescent : baseEnd_4713814 < baseStart_4713814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713826 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_4713826 : Nat := 118140960795 + 4713826 * 2 ^ 59
def prefixEnd_4713826 : Nat := 4983230072969 + 3 ^ 40 * 4713826 * 2
def baseEnd_4713826 : Nat := 2420458459660779367796515

theorem tailTrace_4713826 : CollatzResearch.WordTrace tailWord_4713826 prefixEnd_4713826 2420458459660779367796515 := by
  unfold tailWord_4713826
  simp only [CollatzResearch.WordTrace]
  refine ⟨42981839655155233558004333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114618239080413956154678221 42981839655155233558004333)
  ·
    refine ⟨16118189870683212584251625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42981839655155233558004333 16118189870683212584251625)
    ·
      refine ⟨12088642403012409438188719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16118189870683212584251625 12088642403012409438188719)
      ·
        refine ⟨18132963604518614157283079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12088642403012409438188719 18132963604518614157283079)
        ·
          refine ⟨27199445406777921235924619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18132963604518614157283079 27199445406777921235924619)
          ·
            refine ⟨40799168110166881853886929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27199445406777921235924619 40799168110166881853886929)
            ·
              refine ⟨30599376082625161390415197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40799168110166881853886929 30599376082625161390415197)
              ·
                refine ⟨11474766030984435521405699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30599376082625161390415197 11474766030984435521405699)
                ·
                  refine ⟨17212149046476653282108549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11474766030984435521405699 17212149046476653282108549)
                  ·
                    refine ⟨3227277946214372490395353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17212149046476653282108549 3227277946214372490395353)
                    ·
                      refine ⟨2420458459660779367796515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227277946214372490395353 2420458459660779367796515)
                      ·
                        rfl

theorem cell23_4713826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_4713826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713826 prefixEnd_4713826 := by exact prefixLift 4713826
  have htrace : WordTrace (prefixWord ++ tailWord_4713826) baseStart_4713826 baseEnd_4713826 := by
    simpa [prefixWord, tailWord_4713826, baseEnd_4713826] using wordTrace_append hprefix tailTrace_4713826
  have hstable : (prefixWord ++ tailWord_4713826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713826).length < 2 ^ (prefixWord ++ tailWord_4713826).sum := by decide
  have hdescent : baseEnd_4713826 < baseStart_4713826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713876 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_4713876 : Nat := 118140960795 + 4713876 * 2 ^ 59
def prefixEnd_4713876 : Nat := 4983230072969 + 3 ^ 40 * 4713876 * 2
def baseEnd_4713876 : Nat := 2420484133693504172171285

theorem tailTrace_4713876 : CollatzResearch.WordTrace tailWord_4713876 prefixEnd_4713876 2420484133693504172171285 := by
  unfold tailWord_4713876
  simp only [CollatzResearch.WordTrace]
  refine ⟨85964591135219896385668741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114619454846959861847558321 85964591135219896385668741)
  ·
    refine ⟨16118360837853730572312889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85964591135219896385668741 16118360837853730572312889)
    ·
      refine ⟨12088770628390297929234667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16118360837853730572312889 12088770628390297929234667)
      ·
        refine ⟨18133155942585446893852001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12088770628390297929234667 18133155942585446893852001)
        ·
          refine ⟨13599866956939085170389001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18133155942585446893852001 13599866956939085170389001)
          ·
            refine ⟨10199900217704313877791751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13599866956939085170389001 10199900217704313877791751)
            ·
              refine ⟨15299850326556470816687627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10199900217704313877791751 15299850326556470816687627)
              ·
                refine ⟨22949775489834706225031441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15299850326556470816687627 22949775489834706225031441)
                ·
                  refine ⟨17212331617376029668773581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22949775489834706225031441 17212331617376029668773581)
                  ·
                    refine ⟨6454624356516011125790093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17212331617376029668773581 6454624356516011125790093)
                    ·
                      refine ⟨2420484133693504172171285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454624356516011125790093 2420484133693504172171285)
                      ·
                        rfl

theorem cell23_4713876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_4713876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713876 prefixEnd_4713876 := by exact prefixLift 4713876
  have htrace : WordTrace (prefixWord ++ tailWord_4713876) baseStart_4713876 baseEnd_4713876 := by
    simpa [prefixWord, tailWord_4713876, baseEnd_4713876] using wordTrace_append hprefix tailTrace_4713876
  have hstable : (prefixWord ++ tailWord_4713876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713876).length < 2 ^ (prefixWord ++ tailWord_4713876).sum := by decide
  have hdescent : baseEnd_4713876 < baseStart_4713876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713896 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4713896 : Nat := 118140960795 + 4713896 * 2 ^ 59
def prefixEnd_4713896 : Nat := 4983230072969 + 3 ^ 40 * 4713896 * 2
def baseEnd_4713896 : Nat := 806831467768864697973731

theorem tailTrace_4713896 : CollatzResearch.WordTrace tailWord_4713896 prefixEnd_4713896 806831467768864697973731 := by
  unfold tailWord_4713896
  simp only [CollatzResearch.WordTrace]
  refine ⟨85964955865183668093532771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114619941153578224124710361 85964955865183668093532771)
  ·
    refine ⟨128947433797775502140299157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85964955865183668093532771 128947433797775502140299157)
    ·
      refine ⟨6044410959270726662826523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128947433797775502140299157 6044410959270726662826523)
      ·
        refine ⟨9066616438906089994239785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6044410959270726662826523 9066616438906089994239785)
        ·
          refine ⟨6799962329179567495679839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9066616438906089994239785 6799962329179567495679839)
          ·
            refine ⟨10199943493769351243519759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6799962329179567495679839 10199943493769351243519759)
            ·
              refine ⟨15299915240654026865279639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10199943493769351243519759 15299915240654026865279639)
              ·
                refine ⟨22949872860981040297919459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15299915240654026865279639 22949872860981040297919459)
                ·
                  refine ⟨34424809291471560446879189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22949872860981040297919459 34424809291471560446879189)
                  ·
                    refine ⟨806831467768864697973731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34424809291471560446879189 806831467768864697973731)
                    ·
                      rfl

theorem cell23_4713896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4713896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713896 prefixEnd_4713896 := by exact prefixLift 4713896
  have htrace : WordTrace (prefixWord ++ tailWord_4713896) baseStart_4713896 baseEnd_4713896 := by
    simpa [prefixWord, tailWord_4713896, baseEnd_4713896] using wordTrace_append hprefix tailTrace_4713896
  have hstable : (prefixWord ++ tailWord_4713896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713896).length < 2 ^ (prefixWord ++ tailWord_4713896).sum := by decide
  have hdescent : baseEnd_4713896 < baseStart_4713896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713912 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_4713912 : Nat := 118140960795 + 4713912 * 2 ^ 59
def prefixEnd_4713912 : Nat := 4983230072969 + 3 ^ 40 * 4713912 * 2
def baseEnd_4713912 : Nat := 2420502618997066031321119

theorem tailTrace_4713912 : CollatzResearch.WordTrace tailWord_4713912 prefixEnd_4713912 2420502618997066031321119 := by
  unfold tailWord_4713912
  simp only [CollatzResearch.WordTrace]
  refine ⟨85965247649154685459823995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114620330198872913946431993 85965247649154685459823995)
  ·
    refine ⟨128947871473732028189735993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85965247649154685459823995 128947871473732028189735993)
    ·
      refine ⟨96710903605299021142301995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128947871473732028189735993 96710903605299021142301995)
      ·
        refine ⟨145066355407948531713452993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96710903605299021142301995 145066355407948531713452993)
        ·
          refine ⟨108799766555961398785089745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145066355407948531713452993 108799766555961398785089745)
          ·
            refine ⟨81599824916971049088817309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108799766555961398785089745 81599824916971049088817309)
            ·
              refine ⟨30599934343864143408306491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81599824916971049088817309 30599934343864143408306491)
              ·
                refine ⟨45899901515796215112459737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30599934343864143408306491 45899901515796215112459737)
                ·
                  refine ⟨34424926136847161334344803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45899901515796215112459737 34424926136847161334344803)
                  ·
                    refine ⟨51637389205270742001517205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34424926136847161334344803 51637389205270742001517205)
                    ·
                      refine ⟨2420502618997066031321119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51637389205270742001517205 2420502618997066031321119)
                      ·
                        rfl

theorem cell23_4713912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_4713912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713912 prefixEnd_4713912 := by exact prefixLift 4713912
  have htrace : WordTrace (prefixWord ++ tailWord_4713912) baseStart_4713912 baseEnd_4713912 := by
    simpa [prefixWord, tailWord_4713912, baseEnd_4713912] using wordTrace_append hprefix tailTrace_4713912
  have hstable : (prefixWord ++ tailWord_4713912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713912).length < 2 ^ (prefixWord ++ tailWord_4713912).sum := by decide
  have hdescent : baseEnd_4713912 < baseStart_4713912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713919 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 3]
def baseStart_4713919 : Nat := 118140960795 + 4713919 * 2 ^ 59
def prefixEnd_4713919 : Nat := 4983230072969 + 3 ^ 40 * 4713919 * 2
def baseEnd_4713919 : Nat := 2420506213361647503933587

theorem tailTrace_4713919 : CollatzResearch.WordTrace tailWord_4713919 prefixEnd_4713919 2420506213361647503933587 := by
  unfold tailWord_4713919
  simp only [CollatzResearch.WordTrace]
  refine ⟨171930750609284011115152811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114620500406189340743435207 171930750609284011115152811)
  ·
    refine ⟨257896125913926016672729217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171930750609284011115152811 257896125913926016672729217)
    ·
      refine ⟨193422094435444512504546913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257896125913926016672729217 193422094435444512504546913)
      ·
        refine ⟨145066570826583384378410185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193422094435444512504546913 145066570826583384378410185)
        ·
          refine ⟨108799928119937538283807639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145066570826583384378410185 108799928119937538283807639)
          ·
            refine ⟨163199892179906307425711459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108799928119937538283807639 163199892179906307425711459)
            ·
              refine ⟨244799838269859461138567189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163199892179906307425711459 244799838269859461138567189)
              ·
                refine ⟨11474992418899662240870337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 244799838269859461138567189 11474992418899662240870337)
                ·
                  refine ⟨8606244314174746680652753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11474992418899662240870337 8606244314174746680652753)
                  ·
                    refine ⟨6454683235631060010489565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8606244314174746680652753 6454683235631060010489565)
                    ·
                      refine ⟨2420506213361647503933587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454683235631060010489565 2420506213361647503933587)
                      ·
                        rfl

theorem cell23_4713919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_4713919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713919 prefixEnd_4713919 := by exact prefixLift 4713919
  have htrace : WordTrace (prefixWord ++ tailWord_4713919) baseStart_4713919 baseEnd_4713919 := by
    simpa [prefixWord, tailWord_4713919, baseEnd_4713919] using wordTrace_append hprefix tailTrace_4713919
  have hstable : (prefixWord ++ tailWord_4713919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713919).length < 2 ^ (prefixWord ++ tailWord_4713919).sum := by decide
  have hdescent : baseEnd_4713919 < baseStart_4713919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713976 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 4, 3, 2]
def baseStart_4713976 : Nat := 118140960795 + 4713976 * 2 ^ 59
def prefixEnd_4713976 : Nat := 4983230072969 + 3 ^ 40 * 4713976 * 2
def baseEnd_4713976 : Nat := 2420535481758953780920825

theorem tailTrace_4713976 : CollatzResearch.WordTrace tailWord_4713976 prefixEnd_4713976 2420535481758953780920825 := by
  unfold tailWord_4713976
  simp only [CollatzResearch.WordTrace]
  refine ⟨85966414785038754924988891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114621886380051673233318521 85966414785038754924988891)
  ·
    refine ⟨128949622177558132387483337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85966414785038754924988891 128949622177558132387483337)
    ·
      refine ⟨96712216633168599290612503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128949622177558132387483337 96712216633168599290612503)
      ·
        refine ⟨145068324949752898935918755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96712216633168599290612503 145068324949752898935918755)
        ·
          refine ⟨217602487424629348403878133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145068324949752898935918755 217602487424629348403878133)
          ·
            refine ⟨20400233196059001412863575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217602487424629348403878133 20400233196059001412863575)
            ·
              refine ⟨30600349794088502119295363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20400233196059001412863575 30600349794088502119295363)
              ·
                refine ⟨45900524691132753178943045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30600349794088502119295363 45900524691132753178943045)
                ·
                  refine ⟨8606348379587391221051821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45900524691132753178943045 8606348379587391221051821)
                  ·
                    refine ⟨3227380642345271707894433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8606348379587391221051821 3227380642345271707894433)
                    ·
                      refine ⟨2420535481758953780920825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227380642345271707894433 2420535481758953780920825)
                      ·
                        rfl

theorem cell23_4713976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_4713976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713976 prefixEnd_4713976 := by exact prefixLift 4713976
  have htrace : WordTrace (prefixWord ++ tailWord_4713976) baseStart_4713976 baseEnd_4713976 := by
    simpa [prefixWord, tailWord_4713976, baseEnd_4713976] using wordTrace_append hprefix tailTrace_4713976
  have hstable : (prefixWord ++ tailWord_4713976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713976).length < 2 ^ (prefixWord ++ tailWord_4713976).sum := by decide
  have hdescent : baseEnd_4713976 < baseStart_4713976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713989 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_4713989 : Nat := 118140960795 + 4713989 * 2 ^ 59
def prefixEnd_4713989 : Nat := 4983230072969 + 3 ^ 40 * 4713989 * 2
def baseEnd_4713989 : Nat := 2420542157007462230058265

theorem tailTrace_4713989 : CollatzResearch.WordTrace tailWord_4713989 prefixEnd_4713989 2420542157007462230058265 := by
  unfold tailWord_4713989
  simp only [CollatzResearch.WordTrace]
  refine ⟨171933303719030413070201021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114622202479353608713467347 171933303719030413070201021)
  ·
    refine ⟨64474988894636404901325383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171933303719030413070201021 64474988894636404901325383)
    ·
      refine ⟨96712483341954607351988075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64474988894636404901325383 96712483341954607351988075)
      ·
        refine ⟨145068725012931911027982113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96712483341954607351988075 145068725012931911027982113)
        ·
          refine ⟨108801543759698933270986585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145068725012931911027982113 108801543759698933270986585)
          ·
            refine ⟨81601157819774199953239939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108801543759698933270986585 81601157819774199953239939)
            ·
              refine ⟨122401736729661299929859909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81601157819774199953239939 122401736729661299929859909)
              ·
                refine ⟨22950325636811493736848733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122401736729661299929859909 22950325636811493736848733)
                ·
                  refine ⟨8606372113804310151318275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22950325636811493736848733 8606372113804310151318275)
                  ·
                    refine ⟨12909558170706465226977413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8606372113804310151318275 12909558170706465226977413)
                    ·
                      refine ⟨2420542157007462230058265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12909558170706465226977413 2420542157007462230058265)
                      ·
                        rfl

theorem cell23_4713989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_4713989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713989 prefixEnd_4713989 := by exact prefixLift 4713989
  have htrace : WordTrace (prefixWord ++ tailWord_4713989) baseStart_4713989 baseEnd_4713989 := by
    simpa [prefixWord, tailWord_4713989, baseEnd_4713989] using wordTrace_append hprefix tailTrace_4713989
  have hstable : (prefixWord ++ tailWord_4713989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713989).length < 2 ^ (prefixWord ++ tailWord_4713989).sum := by decide
  have hdescent : baseEnd_4713989 < baseStart_4713989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714016 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 1, 6]
def baseStart_4714016 : Nat := 118140960795 + 4714016 * 2 ^ 59
def prefixEnd_4714016 : Nat := 4983230072969 + 3 ^ 40 * 4714016 * 2
def baseEnd_4714016 : Nat := 806852006995044541473547

theorem tailTrace_4714016 : CollatzResearch.WordTrace tailWord_4714016 prefixEnd_4714016 806852006995044541473547 := by
  unfold tailWord_4714016
  simp only [CollatzResearch.WordTrace]
  refine ⟨85967144244966298340716951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114622858993288397787622601 85967144244966298340716951)
  ·
    refine ⟨128950716367449447511075427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85967144244966298340716951 128950716367449447511075427)
    ·
      refine ⟨193426074551174171266613141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128950716367449447511075427 193426074551174171266613141)
      ·
        refine ⟨9066847244586289278122491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193426074551174171266613141 9066847244586289278122491)
        ·
          refine ⟨13600270866879433917183737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9066847244586289278122491 13600270866879433917183737)
          ·
            refine ⟨10200203150159575437887803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13600270866879433917183737 10200203150159575437887803)
            ·
              refine ⟨15300304725239363156831705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10200203150159575437887803 15300304725239363156831705)
              ·
                refine ⟨11475228543929522367623779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15300304725239363156831705 11475228543929522367623779)
                ·
                  refine ⟨17212842815894283551435669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11475228543929522367623779 17212842815894283551435669)
                  ·
                    refine ⟨806852006995044541473547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17212842815894283551435669 806852006995044541473547)
                    ·
                      rfl

theorem cell23_4714016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_4714016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714016 prefixEnd_4714016 := by exact prefixLift 4714016
  have htrace : WordTrace (prefixWord ++ tailWord_4714016) baseStart_4714016 baseEnd_4714016 := by
    simpa [prefixWord, tailWord_4714016, baseEnd_4714016] using wordTrace_append hprefix tailTrace_4714016
  have hstable : (prefixWord ++ tailWord_4714016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714016).length < 2 ^ (prefixWord ++ tailWord_4714016).sum := by decide
  have hdescent : baseEnd_4714016 < baseStart_4714016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714056 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_4714056 : Nat := 118140960795 + 4714056 * 2 ^ 59
def prefixEnd_4714056 : Nat := 4983230072969 + 3 ^ 40 * 4714056 * 2
def baseEnd_4714056 : Nat := 2420576560211313467920457

theorem tailTrace_4714056 : CollatzResearch.WordTrace tailWord_4714056 prefixEnd_4714056 2420576560211313467920457 := by
  unfold tailWord_4714056
  simp only [CollatzResearch.WordTrace]
  refine ⟨85967873704893841756445011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114623831606525122341926681 85967873704893841756445011)
  ·
    refine ⟨128951810557340762634667517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85967873704893841756445011 128951810557340762634667517)
    ·
      refine ⟨48356928959002785988000319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128951810557340762634667517 48356928959002785988000319)
      ·
        refine ⟨72535393438504178982000479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48356928959002785988000319 72535393438504178982000479)
        ·
          refine ⟨108803090157756268473000719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72535393438504178982000479 108803090157756268473000719)
          ·
            refine ⟨163204635236634402709501079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108803090157756268473000719 163204635236634402709501079)
            ·
              refine ⟨244806952854951604064251619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163204635236634402709501079 244806952854951604064251619)
              ·
                refine ⟨367210429282427406096377429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244806952854951604064251619 367210429282427406096377429)
                ·
                  refine ⟨4303247218153446165191923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 367210429282427406096377429 4303247218153446165191923)
                  ·
                    refine ⟨6454870827230169247787885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4303247218153446165191923 6454870827230169247787885)
                    ·
                      refine ⟨2420576560211313467920457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454870827230169247787885 2420576560211313467920457)
                      ·
                        rfl

theorem cell23_4714056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_4714056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714056 prefixEnd_4714056 := by exact prefixLift 4714056
  have htrace : WordTrace (prefixWord ++ tailWord_4714056) baseStart_4714056 baseEnd_4714056 := by
    simpa [prefixWord, tailWord_4714056, baseEnd_4714056] using wordTrace_append hprefix tailTrace_4714056
  have hstable : (prefixWord ++ tailWord_4714056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714056).length < 2 ^ (prefixWord ++ tailWord_4714056).sum := by decide
  have hdescent : baseEnd_4714056 < baseStart_4714056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714069 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4714069 : Nat := 118140960795 + 4714069 * 2 ^ 59
def prefixEnd_4714069 : Nat := 4983230072969 + 3 ^ 40 * 4714069 * 2
def baseEnd_4714069 : Nat := 2420583235459821917057897

theorem tailTrace_4714069 : CollatzResearch.WordTrace tailWord_4714069 prefixEnd_4714069 2420583235459821917057897 := by
  unfold tailWord_4714069
  simp only [CollatzResearch.WordTrace]
  refine ⟨171936221558740586733113261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114624147705827057822075507 171936221558740586733113261)
  ·
    refine ⟨64476083084527720024917473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171936221558740586733113261 64476083084527720024917473)
    ·
      refine ⟨48357062313395790018688105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64476083084527720024917473 48357062313395790018688105)
      ·
        refine ⟨36267796735046842514016079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48357062313395790018688105 36267796735046842514016079)
        ·
          refine ⟨54401695102570263771024119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36267796735046842514016079 54401695102570263771024119)
          ·
            refine ⟨81602542653855395656536179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54401695102570263771024119 81602542653855395656536179)
            ·
              refine ⟨122403813980783093484804269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81602542653855395656536179 122403813980783093484804269)
              ·
                refine ⟨45901430242793660056801601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122403813980783093484804269 45901430242793660056801601)
                ·
                  refine ⟨34426072682095245042601201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45901430242793660056801601 34426072682095245042601201)
                  ·
                    refine ⟨25819554511571433781950901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34426072682095245042601201 25819554511571433781950901)
                    ·
                      refine ⟨2420583235459821917057897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25819554511571433781950901 2420583235459821917057897)
                      ·
                        rfl

theorem cell23_4714069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4714069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714069 prefixEnd_4714069 := by exact prefixLift 4714069
  have htrace : WordTrace (prefixWord ++ tailWord_4714069) baseStart_4714069 baseEnd_4714069 := by
    simpa [prefixWord, tailWord_4714069, baseEnd_4714069] using wordTrace_append hprefix tailTrace_4714069
  have hstable : (prefixWord ++ tailWord_4714069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714069).length < 2 ^ (prefixWord ++ tailWord_4714069).sum := by decide
  have hdescent : baseEnd_4714069 < baseStart_4714069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714077 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4714077 : Nat := 118140960795 + 4714077 * 2 ^ 59
def prefixEnd_4714077 : Nat := 4983230072969 + 3 ^ 40 * 4714077 * 2
def baseEnd_4714077 : Nat := 2420587343305057885757861

theorem tailTrace_4714077 : CollatzResearch.WordTrace tailWord_4714077 prefixEnd_4714077 2420587343305057885757861 := by
  unfold tailWord_4714077
  simp only [CollatzResearch.WordTrace]
  refine ⟨171936513342711604099404485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114624342228474402732936323 171936513342711604099404485)
  ·
    refine ⟨32238096251758425768638341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171936513342711604099404485 32238096251758425768638341)
    ·
      refine ⟨6044643047204704831619689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32238096251758425768638341 6044643047204704831619689)
      ·
        refine ⟨4533482285403528623714767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6044643047204704831619689 4533482285403528623714767)
        ·
          refine ⟨6800223428105292935572151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4533482285403528623714767 6800223428105292935572151)
          ·
            refine ⟨10200335142157939403358227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6800223428105292935572151 10200335142157939403358227)
            ·
              refine ⟨15300502713236909105037341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10200335142157939403358227 15300502713236909105037341)
              ·
                refine ⟨5737688517463840914389003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15300502713236909105037341 5737688517463840914389003)
                ·
                  refine ⟨8606532776195761371583505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5737688517463840914389003 8606532776195761371583505)
                  ·
                    refine ⟨6454899582146821028687629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8606532776195761371583505 6454899582146821028687629)
                    ·
                      refine ⟨2420587343305057885757861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454899582146821028687629 2420587343305057885757861)
                      ·
                        rfl

theorem cell23_4714077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4714077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714077 prefixEnd_4714077 := by exact prefixLift 4714077
  have htrace : WordTrace (prefixWord ++ tailWord_4714077) baseStart_4714077 baseEnd_4714077 := by
    simpa [prefixWord, tailWord_4714077, baseEnd_4714077] using wordTrace_append hprefix tailTrace_4714077
  have hstable : (prefixWord ++ tailWord_4714077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714077).length < 2 ^ (prefixWord ++ tailWord_4714077).sum := by decide
  have hdescent : baseEnd_4714077 < baseStart_4714077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714089 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 2, 6]
def baseStart_4714089 : Nat := 118140960795 + 4714089 * 2 ^ 59
def prefixEnd_4714089 : Nat := 4983230072969 + 3 ^ 40 * 4714089 * 2
def baseEnd_4714089 : Nat := 806864501690970612935935

theorem tailTrace_4714089 : CollatzResearch.WordTrace tailWord_4714089 prefixEnd_4714089 806864501690970612935935 := by
  unfold tailWord_4714089
  simp only [CollatzResearch.WordTrace]
  refine ⟨171936951018668130148841321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114624634012445420099227547 171936951018668130148841321)
  ·
    refine ⟨128952713264001097611630991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171936951018668130148841321 128952713264001097611630991)
    ·
      refine ⟨193429069896001646417446487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128952713264001097611630991 193429069896001646417446487)
      ·
        refine ⟨290143604844002469626169731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193429069896001646417446487 290143604844002469626169731)
        ·
          refine ⟨435215407266003704439254597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290143604844002469626169731 435215407266003704439254597)
          ·
            refine ⟨81602888862375694582360237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 435215407266003704439254597 81602888862375694582360237)
            ·
              refine ⟨30601083323390885468385089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81602888862375694582360237 30601083323390885468385089)
              ·
                refine ⟨22950812492543164101288817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30601083323390885468385089 22950812492543164101288817)
                ·
                  refine ⟨17213109369407373075966613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22950812492543164101288817 17213109369407373075966613)
                  ·
                    refine ⟨806864501690970612935935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17213109369407373075966613 806864501690970612935935)
                    ·
                      rfl

theorem cell23_4714089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_4714089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714089 prefixEnd_4714089 := by exact prefixLift 4714089
  have htrace : WordTrace (prefixWord ++ tailWord_4714089) baseStart_4714089 baseEnd_4714089 := by
    simpa [prefixWord, tailWord_4714089, baseEnd_4714089] using wordTrace_append hprefix tailTrace_4714089
  have hstable : (prefixWord ++ tailWord_4714089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714089).length < 2 ^ (prefixWord ++ tailWord_4714089).sum := by decide
  have hdescent : baseEnd_4714089 < baseStart_4714089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714090 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_4714090 : Nat := 118140960795 + 4714090 * 2 ^ 59
def prefixEnd_4714090 : Nat := 4983230072969 + 3 ^ 40 * 4714090 * 2
def baseEnd_4714090 : Nat := 2420594018553566334895301

theorem tailTrace_4714090 : CollatzResearch.WordTrace tailWord_4714090 prefixEnd_4714090 2420594018553566334895301 := by
  unfold tailWord_4714090
  simp only [CollatzResearch.WordTrace]
  refine ⟨42984246872916126829906931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114624658327776338213085149 42984246872916126829906931)
  ·
    refine ⟨64476370309374190244860397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42984246872916126829906931 64476370309374190244860397)
    ·
      refine ⟨24178638866015321341822649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64476370309374190244860397 24178638866015321341822649)
      ·
        refine ⟨18133979149511491006366987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24178638866015321341822649 18133979149511491006366987)
        ·
          refine ⟨27200968724267236509550481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18133979149511491006366987 27200968724267236509550481)
          ·
            refine ⟨20400726543200427382162861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27200968724267236509550481 20400726543200427382162861)
            ·
              refine ⟨7650272453700160268311073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20400726543200427382162861 7650272453700160268311073)
              ·
                refine ⟨5737704340275120201233305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7650272453700160268311073 5737704340275120201233305)
                ·
                  refine ⟨4303278255206340150924979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5737704340275120201233305 4303278255206340150924979)
                  ·
                    refine ⟨6454917382809510226387469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4303278255206340150924979 6454917382809510226387469)
                    ·
                      refine ⟨2420594018553566334895301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6454917382809510226387469 2420594018553566334895301)
                      ·
                        rfl

theorem cell23_4714090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_4714090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714090 prefixEnd_4714090 := by exact prefixLift 4714090
  have htrace : WordTrace (prefixWord ++ tailWord_4714090) baseStart_4714090 baseEnd_4714090 := by
    simpa [prefixWord, tailWord_4714090, baseEnd_4714090] using wordTrace_append hprefix tailTrace_4714090
  have hstable : (prefixWord ++ tailWord_4714090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714090).length < 2 ^ (prefixWord ++ tailWord_4714090).sum := by decide
  have hdescent : baseEnd_4714090 < baseStart_4714090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714204 : List Nat := [2, 2, 5, 1, 2, 2, 2, 2, 5]
def baseStart_4714204 : Nat := 118140960795 + 4714204 * 2 ^ 59
def prefixEnd_4714204 : Nat := 4983230072969 + 3 ^ 40 * 4714204 * 2
def baseEnd_4714204 : Nat := 268961395038686543207753

theorem tailTrace_4714204 : CollatzResearch.WordTrace tailWord_4714204 prefixEnd_4714204 268961395038686543207753 := by
  unfold tailWord_4714204
  simp only [CollatzResearch.WordTrace]
  refine ⟨85970572706625752394638833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114627430275501003192851777 85970572706625752394638833)
  ·
    refine ⟨64477929529969314295979125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85970572706625752394638833 64477929529969314295979125)
    ·
      refine ⟨6044805893434623215248043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64477929529969314295979125 6044805893434623215248043)
      ·
        refine ⟨9067208840151934822872065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6044805893434623215248043 9067208840151934822872065)
        ·
          refine ⟨6800406630113951117154049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9067208840151934822872065 6800406630113951117154049)
          ·
            refine ⟨5100304972585463337865537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6800406630113951117154049 5100304972585463337865537)
            ·
              refine ⟨3825228729439097503399153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5100304972585463337865537 3825228729439097503399153)
              ·
                refine ⟨2868921547079323127549365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825228729439097503399153 2868921547079323127549365)
                ·
                  refine ⟨268961395038686543207753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2868921547079323127549365 268961395038686543207753)
                  ·
                    rfl

theorem cell23_4714204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_4714204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714204 prefixEnd_4714204 := by exact prefixLift 4714204
  have htrace : WordTrace (prefixWord ++ tailWord_4714204) baseStart_4714204 baseEnd_4714204 := by
    simpa [prefixWord, tailWord_4714204, baseEnd_4714204] using wordTrace_append hprefix tailTrace_4714204
  have hstable : (prefixWord ++ tailWord_4714204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714204).length < 2 ^ (prefixWord ++ tailWord_4714204).sum := by decide
  have hdescent : baseEnd_4714204 < baseStart_4714204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714213 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_4714213 : Nat := 118140960795 + 4714213 * 2 ^ 59
def prefixEnd_4714213 : Nat := 4983230072969 + 3 ^ 40 * 4714213 * 2
def baseEnd_4714213 : Nat := 806885725558023117885745

theorem tailTrace_4714213 : CollatzResearch.WordTrace tailWord_4714213 prefixEnd_4714213 806885725558023117885745 := by
  unfold tailWord_4714213
  simp only [CollatzResearch.WordTrace]
  refine ⟨171941473670218899326355293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114627649113479266217570195 171941473670218899326355293)
  ·
    refine ⟨64478052626332087247383235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171941473670218899326355293 64478052626332087247383235)
    ·
      refine ⟨96717078939498130871074853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64478052626332087247383235 96717078939498130871074853)
      ·
        refine ⟨18134452301155899538326535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96717078939498130871074853 18134452301155899538326535)
        ·
          refine ⟨27201678451733849307489803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18134452301155899538326535 27201678451733849307489803)
          ·
            refine ⟨40802517677600773961234705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27201678451733849307489803 40802517677600773961234705)
            ·
              refine ⟨30601888258200580470926029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40802517677600773961234705 30601888258200580470926029)
              ·
                refine ⟨11475708096825217676597261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30601888258200580470926029 11475708096825217676597261)
                ·
                  refine ⟨4303390536309456628723973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11475708096825217676597261 4303390536309456628723973)
                  ·
                    refine ⟨806885725558023117885745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4303390536309456628723973 806885725558023117885745)
                    ·
                      rfl

theorem cell23_4714213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_4714213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714213 prefixEnd_4714213 := by exact prefixLift 4714213
  have htrace : WordTrace (prefixWord ++ tailWord_4714213) baseStart_4714213 baseEnd_4714213 := by
    simpa [prefixWord, tailWord_4714213, baseEnd_4714213] using wordTrace_append hprefix tailTrace_4714213
  have hstable : (prefixWord ++ tailWord_4714213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714213).length < 2 ^ (prefixWord ++ tailWord_4714213).sum := by decide
  have hdescent : baseEnd_4714213 < baseStart_4714213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714230 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_4714230 : Nat := 118140960795 + 4714230 * 2 ^ 59
def prefixEnd_4714230 : Nat := 4983230072969 + 3 ^ 40 * 4714230 * 2
def baseEnd_4714230 : Nat := 806888635281731929048219

theorem tailTrace_4714230 : CollatzResearch.WordTrace tailWord_4714230 prefixEnd_4714230 806888635281731929048219 := by
  unfold tailWord_4714230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10746380856947331951857759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114628062474104874153149429 10746380856947331951857759)
  ·
    refine ⟨16119571285420997927786639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10746380856947331951857759 16119571285420997927786639)
    ·
      refine ⟨24179356928131496891679959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16119571285420997927786639 24179356928131496891679959)
      ·
        refine ⟨36269035392197245337519939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24179356928131496891679959 36269035392197245337519939)
        ·
          refine ⟨54403553088295868006279909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36269035392197245337519939 54403553088295868006279909)
          ·
            refine ⟨10200666204055475251177483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54403553088295868006279909 10200666204055475251177483)
            ·
              refine ⟨15300999306083212876766225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10200666204055475251177483 15300999306083212876766225)
              ·
                refine ⟨11475749479562409657574669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15300999306083212876766225 11475749479562409657574669)
                ·
                  refine ⟨4303406054835903621590501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11475749479562409657574669 4303406054835903621590501)
                  ·
                    refine ⟨806888635281731929048219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4303406054835903621590501 806888635281731929048219)
                    ·
                      rfl

theorem cell23_4714230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_4714230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714230 prefixEnd_4714230 := by exact prefixLift 4714230
  have htrace : WordTrace (prefixWord ++ tailWord_4714230) baseStart_4714230 baseEnd_4714230 := by
    simpa [prefixWord, tailWord_4714230, baseEnd_4714230] using wordTrace_append hprefix tailTrace_4714230
  have hstable : (prefixWord ++ tailWord_4714230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714230).length < 2 ^ (prefixWord ++ tailWord_4714230).sum := by decide
  have hdescent : baseEnd_4714230 < baseStart_4714230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714280 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_4714280 : Nat := 118140960795 + 4714280 * 2 ^ 59
def prefixEnd_4714280 : Nat := 4983230072969 + 3 ^ 40 * 4714280 * 2
def baseEnd_4714280 : Nat := 2420691579877920591519427

theorem tailTrace_4714280 : CollatzResearch.WordTrace tailWord_4714280 prefixEnd_4714280 2420691579877920591519427 := by
  unfold tailWord_4714280
  simp only [CollatzResearch.WordTrace]
  refine ⟨85971958680488084884522147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114629278240650779846029529 85971958680488084884522147)
  ·
    refine ⟨128957938020732127326783221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85971958680488084884522147 128957938020732127326783221)
    ·
      refine ⟨12089806689443636936885927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128957938020732127326783221 12089806689443636936885927)
      ·
        refine ⟨18134710034165455405328891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12089806689443636936885927 18134710034165455405328891)
        ·
          refine ⟨27202065051248183107993337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18134710034165455405328891 27202065051248183107993337)
          ·
            refine ⟨20401548788436137330995003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27202065051248183107993337 20401548788436137330995003)
            ·
              refine ⟨30602323182654205996492505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20401548788436137330995003 30602323182654205996492505)
              ·
                refine ⟨22951742386990654497369379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30602323182654205996492505 22951742386990654497369379)
                ·
                  refine ⟨34427613580485981746054069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22951742386990654497369379 34427613580485981746054069)
                  ·
                    refine ⟨3227588773170560788692569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34427613580485981746054069 3227588773170560788692569)
                    ·
                      refine ⟨2420691579877920591519427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227588773170560788692569 2420691579877920591519427)
                      ·
                        rfl

theorem cell23_4714280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_4714280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714280 prefixEnd_4714280 := by exact prefixLift 4714280
  have htrace : WordTrace (prefixWord ++ tailWord_4714280) baseStart_4714280 baseEnd_4714280 := by
    simpa [prefixWord, tailWord_4714280, baseEnd_4714280] using wordTrace_append hprefix tailTrace_4714280
  have hstable : (prefixWord ++ tailWord_4714280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714280).length < 2 ^ (prefixWord ++ tailWord_4714280).sum := by decide
  have hdescent : baseEnd_4714280 < baseStart_4714280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714290 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_4714290 : Nat := 118140960795 + 4714290 * 2 ^ 59
def prefixEnd_4714290 : Nat := 4983230072969 + 3 ^ 40 * 4714290 * 2
def baseEnd_4714290 : Nat := 806898904894821850798127

theorem tailTrace_4714290 : CollatzResearch.WordTrace tailWord_4714290 prefixEnd_4714290 806898904894821850798127 := by
  unfold tailWord_4714290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42986070522734985369227081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114629521393959960984605549 42986070522734985369227081)
  ·
    refine ⟨32239552892051239026920311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42986070522734985369227081 32239552892051239026920311)
    ·
      refine ⟨48359329338076858540380467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32239552892051239026920311 48359329338076858540380467)
      ·
        refine ⟨72538994007115287810570701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48359329338076858540380467 72538994007115287810570701)
        ·
          refine ⟨27202122752668232928964013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72538994007115287810570701 27202122752668232928964013)
          ·
            refine ⟨10200796032250587348361505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27202122752668232928964013 10200796032250587348361505)
            ·
              refine ⟨7650597024187940511271129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10200796032250587348361505 7650597024187940511271129)
              ·
                refine ⟨5737947768140955383453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7650597024187940511271129 5737947768140955383453347)
                ·
                  refine ⟨8606921652211433075180021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5737947768140955383453347 8606921652211433075180021)
                  ·
                    refine ⟨806898904894821850798127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8606921652211433075180021 806898904894821850798127)
                    ·
                      rfl

theorem cell23_4714290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_4714290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714290 prefixEnd_4714290 := by exact prefixLift 4714290
  have htrace : WordTrace (prefixWord ++ tailWord_4714290) baseStart_4714290 baseEnd_4714290 := by
    simpa [prefixWord, tailWord_4714290, baseEnd_4714290] using wordTrace_append hprefix tailTrace_4714290
  have hstable : (prefixWord ++ tailWord_4714290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714290).length < 2 ^ (prefixWord ++ tailWord_4714290).sum := by decide
  have hdescent : baseEnd_4714290 < baseStart_4714290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714313 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 5]
def baseStart_4714313 : Nat := 118140960795 + 4714313 * 2 ^ 59
def prefixEnd_4714313 : Nat := 4983230072969 + 3 ^ 40 * 4714313 * 2
def baseEnd_4714313 : Nat := 2420708524739518962406775

theorem tailTrace_4714313 : CollatzResearch.WordTrace tailWord_4714313 prefixEnd_4714313 2420708524739518962406775 := by
  unfold tailWord_4714313
  simp only [CollatzResearch.WordTrace]
  refine ⟨171945120969856616404995593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114630080646571077603330395 171945120969856616404995593)
  ·
    refine ⟨128958840727392462303746695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171945120969856616404995593 128958840727392462303746695)
    ·
      refine ⟨193438261091088693455620043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128958840727392462303746695 193438261091088693455620043)
      ·
        refine ⟨290157391636633040183430065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193438261091088693455620043 290157391636633040183430065)
        ·
          refine ⟨217618043727474780137572549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290157391636633040183430065 217618043727474780137572549)
          ·
            refine ⟨40803383198901521275794853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217618043727474780137572549 40803383198901521275794853)
            ·
              refine ⟨7650634349794035239211535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40803383198901521275794853 7650634349794035239211535)
              ·
                refine ⟨11475951524691052858817303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7650634349794035239211535 11475951524691052858817303)
                ·
                  refine ⟨17213927287036579288225955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11475951524691052858817303 17213927287036579288225955)
                  ·
                    refine ⟨25820890930554868932338933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17213927287036579288225955 25820890930554868932338933)
                    ·
                      refine ⟨2420708524739518962406775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25820890930554868932338933 2420708524739518962406775)
                      ·
                        rfl

theorem cell23_4714313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_4714313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714313 prefixEnd_4714313 := by exact prefixLift 4714313
  have htrace : WordTrace (prefixWord ++ tailWord_4714313) baseStart_4714313 baseEnd_4714313 := by
    simpa [prefixWord, tailWord_4714313, baseEnd_4714313] using wordTrace_append hprefix tailTrace_4714313
  have hstable : (prefixWord ++ tailWord_4714313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714313).length < 2 ^ (prefixWord ++ tailWord_4714313).sum := by decide
  have hdescent : baseEnd_4714313 < baseStart_4714313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714377 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 3]
def baseStart_4714377 : Nat := 118140960795 + 4714377 * 2 ^ 59
def prefixEnd_4714377 : Nat := 4983230072969 + 3 ^ 40 * 4714377 * 2
def baseEnd_4714377 : Nat := 2420741387501406712006481

theorem tailTrace_4714377 : CollatzResearch.WordTrace tailWord_4714377 prefixEnd_4714377 2420741387501406712006481 := by
  unfold tailWord_4714377
  simp only [CollatzResearch.WordTrace]
  refine ⟨171947455241624755335325385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114631636827749836890216923 171947455241624755335325385)
  ·
    refine ⟨128960591431218566501494039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171947455241624755335325385 128960591431218566501494039)
    ·
      refine ⟨193440887146827849752241059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128960591431218566501494039 193440887146827849752241059)
      ·
        refine ⟨290161330720241774628361589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193440887146827849752241059 290161330720241774628361589)
        ·
          refine ⟨27202624755022666371408899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 290161330720241774628361589 27202624755022666371408899)
          ·
            refine ⟨40803937132533999557113349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27202624755022666371408899 40803937132533999557113349)
            ·
              refine ⟨7650738212350124916958753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40803937132533999557113349 7650738212350124916958753)
              ·
                refine ⟨5738053659262593687719065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7650738212350124916958753 5738053659262593687719065)
                ·
                  refine ⟨4303540244446945265789299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5738053659262593687719065 4303540244446945265789299)
                  ·
                    refine ⟨6455310366670417898683949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4303540244446945265789299 6455310366670417898683949)
                    ·
                      refine ⟨2420741387501406712006481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6455310366670417898683949 2420741387501406712006481)
                      ·
                        rfl

theorem cell23_4714377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 3].length) (baseStart_4714377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714377 prefixEnd_4714377 := by exact prefixLift 4714377
  have htrace : WordTrace (prefixWord ++ tailWord_4714377) baseStart_4714377 baseEnd_4714377 := by
    simpa [prefixWord, tailWord_4714377, baseEnd_4714377] using wordTrace_append hprefix tailTrace_4714377
  have hstable : (prefixWord ++ tailWord_4714377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714377).length < 2 ^ (prefixWord ++ tailWord_4714377).sum := by decide
  have hdescent : baseEnd_4714377 < baseStart_4714377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714403 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 3]
def baseStart_4714403 : Nat := 118140960795 + 4714403 * 2 ^ 59
def prefixEnd_4714403 : Nat := 4983230072969 + 3 ^ 40 * 4714403 * 2
def baseEnd_4714403 : Nat := 2420754737998423610281361

theorem tailTrace_4714403 : CollatzResearch.WordTrace tailWord_4714403 prefixEnd_4714403 2420754737998423610281361 := by
  unfold tailWord_4714403
  simp only [CollatzResearch.WordTrace]
  refine ⟨171948403539530561775771863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114632269026353707850514575 171948403539530561775771863)
  ·
    refine ⟨257922605309295842663657795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171948403539530561775771863 257922605309295842663657795)
    ·
      refine ⟨386883907963943763995486693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257922605309295842663657795 386883907963943763995486693)
      ·
        refine ⟨72540732743239455749153755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 386883907963943763995486693 72540732743239455749153755)
        ·
          refine ⟨108811099114859183623730633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72540732743239455749153755 108811099114859183623730633)
          ·
            refine ⟨81608324336144387717797975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108811099114859183623730633 81608324336144387717797975)
            ·
              refine ⟨122412486504216581576696963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81608324336144387717797975 122412486504216581576696963)
              ·
                refine ⟨183618729756324872365045445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122412486504216581576696963 183618729756324872365045445)
                ·
                  refine ⟨34428511829310913568446021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183618729756324872365045445 34428511829310913568446021)
                  ·
                    refine ⟨6455345967995796294083629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34428511829310913568446021 6455345967995796294083629)
                    ·
                      refine ⟨2420754737998423610281361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6455345967995796294083629 2420754737998423610281361)
                      ·
                        rfl

theorem cell23_4714403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_4714403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714403 prefixEnd_4714403 := by exact prefixLift 4714403
  have htrace : WordTrace (prefixWord ++ tailWord_4714403) baseStart_4714403 baseEnd_4714403 := by
    simpa [prefixWord, tailWord_4714403, baseEnd_4714403] using wordTrace_append hprefix tailTrace_4714403
  have hstable : (prefixWord ++ tailWord_4714403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714403).length < 2 ^ (prefixWord ++ tailWord_4714403).sum := by decide
  have hdescent : baseEnd_4714403 < baseStart_4714403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714417 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 1, 4, 2]
def baseStart_4714417 : Nat := 118140960795 + 4714417 * 2 ^ 59
def prefixEnd_4714417 : Nat := 4983230072969 + 3 ^ 40 * 4714417 * 2
def baseEnd_4714417 : Nat := 2420761926727586555506297

theorem tailTrace_4714417 : CollatzResearch.WordTrace tailWord_4714417 prefixEnd_4714417 2420761926727586555506297 := by
  unfold tailWord_4714417
  simp only [CollatzResearch.WordTrace]
  refine ⟨171948914161479842166781505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114632609440986561444521003 171948914161479842166781505)
  ·
    refine ⟨128961685621109881625086129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171948914161479842166781505 128961685621109881625086129)
    ·
      refine ⟨96721264215832411218814597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128961685621109881625086129 96721264215832411218814597)
      ·
        refine ⟨18135237040468577103527737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96721264215832411218814597 18135237040468577103527737)
        ·
          refine ⟨13601427780351432827645803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18135237040468577103527737 13601427780351432827645803)
          ·
            refine ⟨20402141670527149241468705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13601427780351432827645803 20402141670527149241468705)
            ·
              refine ⟨15301606252895361931101529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20402141670527149241468705 15301606252895361931101529)
              ·
                refine ⟨11476204689671521448326147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15301606252895361931101529 11476204689671521448326147)
                ·
                  refine ⟨17214307034507282172489221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11476204689671521448326147 17214307034507282172489221)
                  ·
                    refine ⟨3227682568970115407341729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17214307034507282172489221 3227682568970115407341729)
                    ·
                      refine ⟨2420761926727586555506297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227682568970115407341729 2420761926727586555506297)
                      ·
                        rfl

theorem cell23_4714417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_4714417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714417 prefixEnd_4714417 := by exact prefixLift 4714417
  have htrace : WordTrace (prefixWord ++ tailWord_4714417) baseStart_4714417 baseEnd_4714417 := by
    simpa [prefixWord, tailWord_4714417, baseEnd_4714417] using wordTrace_append hprefix tailTrace_4714417
  have hstable : (prefixWord ++ tailWord_4714417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714417).length < 2 ^ (prefixWord ++ tailWord_4714417).sum := by decide
  have hdescent : baseEnd_4714417 < baseStart_4714417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714421 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_4714421 : Nat := 118140960795 + 4714421 * 2 ^ 59
def prefixEnd_4714421 : Nat := 4983230072969 + 3 ^ 40 * 4714421 * 2
def baseEnd_4714421 : Nat := 2420763980650204539856279

theorem tailTrace_4714421 : CollatzResearch.WordTrace tailWord_4714421 prefixEnd_4714421 2420763980650204539856279 := by
  unfold tailWord_4714421
  simp only [CollatzResearch.WordTrace]
  refine ⟨171949060053465350849927117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114632706702310233899951411 171949060053465350849927117)
  ·
    refine ⟨64480897520049506568722669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171949060053465350849927117 64480897520049506568722669)
    ·
      refine ⟨24180336570018564963271001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64480897520049506568722669 24180336570018564963271001)
      ·
        refine ⟨18135252427513923722453251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24180336570018564963271001 18135252427513923722453251)
        ·
          refine ⟨27202878641270885583679877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18135252427513923722453251 27202878641270885583679877)
          ·
            refine ⟨5100539745238291046939977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27202878641270885583679877 5100539745238291046939977)
            ·
              refine ⟨3825404808928718285204983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5100539745238291046939977 3825404808928718285204983)
              ·
                refine ⟨5738107213393077427807475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825404808928718285204983 5738107213393077427807475)
                ·
                  refine ⟨8607160820089616141711213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5738107213393077427807475 8607160820089616141711213)
                  ·
                    refine ⟨3227685307533606053141705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8607160820089616141711213 3227685307533606053141705)
                    ·
                      refine ⟨2420763980650204539856279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227685307533606053141705 2420763980650204539856279)
                      ·
                        rfl

theorem cell23_4714421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_4714421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714421 prefixEnd_4714421 := by exact prefixLift 4714421
  have htrace : WordTrace (prefixWord ++ tailWord_4714421) baseStart_4714421 baseEnd_4714421 := by
    simpa [prefixWord, tailWord_4714421, baseEnd_4714421] using wordTrace_append hprefix tailTrace_4714421
  have hstable : (prefixWord ++ tailWord_4714421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714421).length < 2 ^ (prefixWord ++ tailWord_4714421).sum := by decide
  have hdescent : baseEnd_4714421 < baseStart_4714421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714428 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4714428 : Nat := 118140960795 + 4714428 * 2 ^ 59
def prefixEnd_4714428 : Nat := 4983230072969 + 3 ^ 40 * 4714428 * 2
def baseEnd_4714428 : Nat := 2420767575014786012468747

theorem tailTrace_4714428 : CollatzResearch.WordTrace tailWord_4714428 prefixEnd_4714428 2420767575014786012468747 := by
  unfold tailWord_4714428
  simp only [CollatzResearch.WordTrace]
  refine ⟨85974657682219995522715969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114632876909626660696954625 85974657682219995522715969)
  ·
    refine ⟨64480993261664996642036977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85974657682219995522715969 64480993261664996642036977)
    ·
      refine ⟨48360744946248747481527733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64480993261664996642036977 48360744946248747481527733)
      ·
        refine ⟨4533819838710820076393225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48360744946248747481527733 4533819838710820076393225)
        ·
          refine ⟨3400364879033115057294919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4533819838710820076393225 3400364879033115057294919)
          ·
            refine ⟨5100547318549672585942379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400364879033115057294919 5100547318549672585942379)
            ·
              refine ⟨7650820977824508878913569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100547318549672585942379 7650820977824508878913569)
              ·
                refine ⟨5738115733368381659185177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7650820977824508878913569 5738115733368381659185177)
                ·
                  refine ⟨4303586800026286244388883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5738115733368381659185177 4303586800026286244388883)
                  ·
                    refine ⟨6455380200039429366583325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4303586800026286244388883 6455380200039429366583325)
                    ·
                      refine ⟨2420767575014786012468747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6455380200039429366583325 2420767575014786012468747)
                      ·
                        rfl

theorem cell23_4714428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4714428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714428 prefixEnd_4714428 := by exact prefixLift 4714428
  have htrace : WordTrace (prefixWord ++ tailWord_4714428) baseStart_4714428 baseEnd_4714428 := by
    simpa [prefixWord, tailWord_4714428, baseEnd_4714428] using wordTrace_append hprefix tailTrace_4714428
  have hstable : (prefixWord ++ tailWord_4714428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714428).length < 2 ^ (prefixWord ++ tailWord_4714428).sum := by decide
  have hdescent : baseEnd_4714428 < baseStart_4714428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714430 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_4714430 : Nat := 118140960795 + 4714430 * 2 ^ 59
def prefixEnd_4714430 : Nat := 4983230072969 + 3 ^ 40 * 4714430 * 2
def baseEnd_4714430 : Nat := 2420768601976095004643737

theorem tailTrace_4714430 : CollatzResearch.WordTrace tailWord_4714430 prefixEnd_4714430 2420768601976095004643737 := by
  unfold tailWord_4714430
  simp only [CollatzResearch.WordTrace]
  refine ⟨21493673538804093173375593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114632925540288496924669829 21493673538804093173375593)
  ·
    refine ⟨16120255154103069880031695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21493673538804093173375593 16120255154103069880031695)
    ·
      refine ⟨24180382731154604820047543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16120255154103069880031695 24180382731154604820047543)
      ·
        refine ⟨36270574096731907230071315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24180382731154604820047543 36270574096731907230071315)
        ·
          refine ⟨54405861145097860845106973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36270574096731907230071315 54405861145097860845106973)
          ·
            refine ⟨20402197929411697816915115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54405861145097860845106973 20402197929411697816915115)
            ·
              refine ⟨30603296894117546725372673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20402197929411697816915115 30603296894117546725372673)
              ·
                refine ⟨22952472670588160044029505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30603296894117546725372673 22952472670588160044029505)
                ·
                  refine ⟨17214354502941120033022129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22952472670588160044029505 17214354502941120033022129)
                  ·
                    refine ⟨12910765877205840024766597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17214354502941120033022129 12910765877205840024766597)
                    ·
                      refine ⟨2420768601976095004643737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12910765877205840024766597 2420768601976095004643737)
                      ·
                        rfl

theorem cell23_4714430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_4714430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714430 prefixEnd_4714430 := by exact prefixLift 4714430
  have htrace : WordTrace (prefixWord ++ tailWord_4714430) baseStart_4714430 baseEnd_4714430 := by
    simpa [prefixWord, tailWord_4714430, baseEnd_4714430] using wordTrace_append hprefix tailTrace_4714430
  have hstable : (prefixWord ++ tailWord_4714430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714430).length < 2 ^ (prefixWord ++ tailWord_4714430).sum := by decide
  have hdescent : baseEnd_4714430 < baseStart_4714430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714440 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 7]
def baseStart_4714440 : Nat := 118140960795 + 4714440 * 2 ^ 59
def prefixEnd_4714440 : Nat := 4983230072969 + 3 ^ 40 * 4714440 * 2
def baseEnd_4714440 : Nat := 268974859642515551724299

theorem tailTrace_4714440 : CollatzResearch.WordTrace tailWord_4714440 prefixEnd_4714440 268974859642515551724299 := by
  unfold tailWord_4714440
  simp only [CollatzResearch.WordTrace]
  refine ⟨85974876520198258547434387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114633168693597678063245849 85974876520198258547434387)
  ·
    refine ⟨128962314780297387821151581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85974876520198258547434387 128962314780297387821151581)
    ·
      refine ⟨48360868042611520432931843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128962314780297387821151581 48360868042611520432931843)
      ·
        refine ⟨72541302063917280649397765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48360868042611520432931843 72541302063917280649397765)
        ·
          refine ⟨13601494136984490121762081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72541302063917280649397765 13601494136984490121762081)
          ·
            refine ⟨10201120602738367591321561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13601494136984490121762081 10201120602738367591321561)
            ·
              refine ⟨7650840452053775693491171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10201120602738367591321561 7650840452053775693491171)
              ·
                refine ⟨11476260678080663540236757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7650840452053775693491171 11476260678080663540236757)
                ·
                  refine ⟨268974859642515551724299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11476260678080663540236757 268974859642515551724299)
                  ·
                    rfl

theorem cell23_4714440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 7].length) (baseStart_4714440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714440 prefixEnd_4714440 := by exact prefixLift 4714440
  have htrace : WordTrace (prefixWord ++ tailWord_4714440) baseStart_4714440 baseEnd_4714440 := by
    simpa [prefixWord, tailWord_4714440, baseEnd_4714440] using wordTrace_append hprefix tailTrace_4714440
  have hstable : (prefixWord ++ tailWord_4714440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714440).length < 2 ^ (prefixWord ++ tailWord_4714440).sum := by decide
  have hdescent : baseEnd_4714440 < baseStart_4714440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714502 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4714502 : Nat := 118140960795 + 4714502 * 2 ^ 59
def prefixEnd_4714502 : Nat := 4983230072969 + 3 ^ 40 * 4714502 * 2
def baseEnd_4714502 : Nat := 2420805572583218722943407

theorem tailTrace_4714502 : CollatzResearch.WordTrace tailWord_4714502 prefixEnd_4714502 2420805572583218722943407 := by
  unfold tailWord_4714502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5373500448942871927613305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114634676244114601122417173 5373500448942871927613305)
  ·
    refine ⟨4030125336707153945709979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5373500448942871927613305 4030125336707153945709979)
    ·
      refine ⟨6045188005060730918564969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030125336707153945709979 6045188005060730918564969)
      ·
        refine ⟨4533891003795548188923727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6045188005060730918564969 4533891003795548188923727)
        ·
          refine ⟨6800836505693322283385591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4533891003795548188923727 6800836505693322283385591)
          ·
            refine ⟨10201254758539983425078387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6800836505693322283385591 10201254758539983425078387)
            ·
              refine ⟨15301882137809975137617581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10201254758539983425078387 15301882137809975137617581)
              ·
                refine ⟨5738205801678740676606593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15301882137809975137617581 5738205801678740676606593)
                ·
                  refine ⟨4303654351259055507454945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5738205801678740676606593 4303654351259055507454945)
                  ·
                    refine ⟨3227740763444291630591209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4303654351259055507454945 3227740763444291630591209)
                    ·
                      refine ⟨2420805572583218722943407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227740763444291630591209 2420805572583218722943407)
                      ·
                        rfl

theorem cell23_4714502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4714502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714502 prefixEnd_4714502 := by exact prefixLift 4714502
  have htrace : WordTrace (prefixWord ++ tailWord_4714502) baseStart_4714502 baseEnd_4714502 := by
    simpa [prefixWord, tailWord_4714502, baseEnd_4714502] using wordTrace_append hprefix tailTrace_4714502
  have hstable : (prefixWord ++ tailWord_4714502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714502).length < 2 ^ (prefixWord ++ tailWord_4714502).sum := by decide
  have hdescent : baseEnd_4714502 < baseStart_4714502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714527 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 3]
def baseStart_4714527 : Nat := 118140960795 + 4714527 * 2 ^ 59
def prefixEnd_4714527 : Nat := 4983230072969 + 3 ^ 40 * 4714527 * 2
def baseEnd_4714527 : Nat := 2420818409599581125130791

theorem tailTrace_4714527 : CollatzResearch.WordTrace tailWord_4714527 prefixEnd_4714527 2420818409599581125130791 := by
  unfold tailWord_4714527
  simp only [CollatzResearch.WordTrace]
  refine ⟨171952926191081330953285835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114635284127387553968857223 171952926191081330953285835)
  ·
    refine ⟨257929389286621996429928753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171952926191081330953285835 257929389286621996429928753)
    ·
      refine ⟨193447041964966497322446565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257929389286621996429928753 193447041964966497322446565)
      ·
        refine ⟨36271320368431218247958731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193447041964966497322446565 36271320368431218247958731)
        ·
          refine ⟨54406980552646827371938097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36271320368431218247958731 54406980552646827371938097)
          ·
            refine ⟨40805235414485120528953573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54406980552646827371938097 40805235414485120528953573)
            ·
              refine ⟨7650981640215960099178795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40805235414485120528953573 7650981640215960099178795)
              ·
                refine ⟨11476472460323940148768193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7650981640215960099178795 11476472460323940148768193)
                ·
                  refine ⟨8607354345242955111576145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11476472460323940148768193 8607354345242955111576145)
                  ·
                    refine ⟨6455515758932216333682109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8607354345242955111576145 6455515758932216333682109)
                    ·
                      refine ⟨2420818409599581125130791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6455515758932216333682109 2420818409599581125130791)
                      ·
                        rfl

theorem cell23_4714527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_4714527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714527 prefixEnd_4714527 := by exact prefixLift 4714527
  have htrace : WordTrace (prefixWord ++ tailWord_4714527) baseStart_4714527 baseEnd_4714527 := by
    simpa [prefixWord, tailWord_4714527, baseEnd_4714527] using wordTrace_append hprefix tailTrace_4714527
  have hstable : (prefixWord ++ tailWord_4714527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714527).length < 2 ^ (prefixWord ++ tailWord_4714527).sum := by decide
  have hdescent : baseEnd_4714527 < baseStart_4714527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714560 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 3, 5]
def baseStart_4714560 : Nat := 118140960795 + 4714560 * 2 ^ 59
def prefixEnd_4714560 : Nat := 4983230072969 + 3 ^ 40 * 4714560 * 2
def baseEnd_4714560 : Nat := 806945118153726498672713

theorem tailTrace_4714560 : CollatzResearch.WordTrace tailWord_4714560 prefixEnd_4714560 806945118153726498672713 := by
  unfold tailWord_4714560
  simp only [CollatzResearch.WordTrace]
  refine ⟨85977064899980888794618567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114636086533307851726158089 85977064899980888794618567)
  ·
    refine ⟨128965597349971333191927851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85977064899980888794618567 128965597349971333191927851)
    ·
      refine ⟨193448396024956999787891777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128965597349971333191927851 193448396024956999787891777)
      ·
        refine ⟨145086297018717749840918833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193448396024956999787891777 145086297018717749840918833)
        ·
          refine ⟨108814722764038312380689125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145086297018717749840918833 108814722764038312380689125)
          ·
            refine ⟨20402760518257183571379211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108814722764038312380689125 20402760518257183571379211)
            ·
              refine ⟨30604140777385775357068817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20402760518257183571379211 30604140777385775357068817)
              ·
                refine ⟨22953105583039331517801613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30604140777385775357068817 22953105583039331517801613)
                ·
                  refine ⟨8607414593639749319175605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22953105583039331517801613 8607414593639749319175605)
                  ·
                    refine ⟨806945118153726498672713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8607414593639749319175605 806945118153726498672713)
                    ·
                      rfl

theorem cell23_4714560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_4714560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714560 prefixEnd_4714560 := by exact prefixLift 4714560
  have htrace : WordTrace (prefixWord ++ tailWord_4714560) baseStart_4714560 baseEnd_4714560 := by
    simpa [prefixWord, tailWord_4714560, baseEnd_4714560] using wordTrace_append hprefix tailTrace_4714560
  have hstable : (prefixWord ++ tailWord_4714560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714560).length < 2 ^ (prefixWord ++ tailWord_4714560).sum := by decide
  have hdescent : baseEnd_4714560 < baseStart_4714560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714567 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_4714567 : Nat := 118140960795 + 4714567 * 2 ^ 59
def prefixEnd_4714567 : Nat := 4983230072969 + 3 ^ 40 * 4714567 * 2
def baseEnd_4714567 : Nat := 2420838948825760968630607

theorem tailTrace_4714567 : CollatzResearch.WordTrace tailWord_4714567 prefixEnd_4714567 2420838948825760968630607 := by
  unfold tailWord_4714567
  simp only [CollatzResearch.WordTrace]
  refine ⟨171954385110936417784741955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114636256740624278523161303 171954385110936417784741955)
  ·
    refine ⟨257931577666404626677112933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171954385110936417784741955 257931577666404626677112933)
    ·
      refine ⟨48362170812450867501958675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257931577666404626677112933 48362170812450867501958675)
      ·
        refine ⟨72543256218676301252938013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48362170812450867501958675 72543256218676301252938013)
        ·
          refine ⟨27203721082003612969851755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72543256218676301252938013 27203721082003612969851755)
          ·
            refine ⟨40805581623005419454777633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27203721082003612969851755 40805581623005419454777633)
            ·
              refine ⟨30604186217254064591083225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40805581623005419454777633 30604186217254064591083225)
              ·
                refine ⟨22953139662940548443312419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30604186217254064591083225 22953139662940548443312419)
                ·
                  refine ⟨34429709494410822664968629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22953139662940548443312419 34429709494410822664968629)
                  ·
                    refine ⟨3227785265101014624840809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34429709494410822664968629 3227785265101014624840809)
                    ·
                      refine ⟨2420838948825760968630607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227785265101014624840809 2420838948825760968630607)
                      ·
                        rfl

theorem cell23_4714567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_4714567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714567 prefixEnd_4714567 := by exact prefixLift 4714567
  have htrace : WordTrace (prefixWord ++ tailWord_4714567) baseStart_4714567 baseEnd_4714567 := by
    simpa [prefixWord, tailWord_4714567, baseEnd_4714567] using wordTrace_append hprefix tailTrace_4714567
  have hstable : (prefixWord ++ tailWord_4714567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714567).length < 2 ^ (prefixWord ++ tailWord_4714567).sum := by decide
  have hdescent : baseEnd_4714567 < baseStart_4714567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714574 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_4714574 : Nat := 118140960795 + 4714574 * 2 ^ 59
def prefixEnd_4714574 : Nat := 4983230072969 + 3 ^ 40 * 4714574 * 2
def baseEnd_4714574 : Nat := 2420842543190342441243075

theorem tailTrace_4714574 : CollatzResearch.WordTrace tailWord_4714574 prefixEnd_4714574 2420842543190342441243075 := by
  unfold tailWord_4714574
  simp only [CollatzResearch.WordTrace]
  refine ⟨21494330052738882247530847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114636426947940705320164517 21494330052738882247530847)
  ·
    refine ⟨32241495079108323371296271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21494330052738882247530847 32241495079108323371296271)
    ·
      refine ⟨48362242618662485056944407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32241495079108323371296271 48362242618662485056944407)
      ·
        refine ⟨72543363927993727585416611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48362242618662485056944407 72543363927993727585416611)
        ·
          refine ⟨108815045891990591378124917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72543363927993727585416611 108815045891990591378124917)
          ·
            refine ⟨10201410552374117941699211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108815045891990591378124917 10201410552374117941699211)
            ·
              refine ⟨15302115828561176912548817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10201410552374117941699211 15302115828561176912548817)
              ·
                refine ⟨11476586871420882684411613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15302115828561176912548817 11476586871420882684411613)
                ·
                  refine ⟨4303720076782831006654355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11476586871420882684411613 4303720076782831006654355)
                  ·
                    refine ⟨6455580115174246509981533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4303720076782831006654355 6455580115174246509981533)
                    ·
                      refine ⟨2420842543190342441243075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6455580115174246509981533 2420842543190342441243075)
                      ·
                        rfl

theorem cell23_4714574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_4714574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714574 prefixEnd_4714574 := by exact prefixLift 4714574
  have htrace : WordTrace (prefixWord ++ tailWord_4714574) baseStart_4714574 baseEnd_4714574 := by
    simpa [prefixWord, tailWord_4714574, baseEnd_4714574] using wordTrace_append hprefix tailTrace_4714574
  have hstable : (prefixWord ++ tailWord_4714574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714574).length < 2 ^ (prefixWord ++ tailWord_4714574).sum := by decide
  have hdescent : baseEnd_4714574 < baseStart_4714574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714584 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 2, 3, 2]
def baseStart_4714584 : Nat := 118140960795 + 4714584 * 2 ^ 59
def prefixEnd_4714584 : Nat := 4983230072969 + 3 ^ 40 * 4714584 * 2
def baseEnd_4714584 : Nat := 2420847677996887402118029

theorem tailTrace_4714584 : CollatzResearch.WordTrace tailWord_4714584 prefixEnd_4714584 2420847677996887402118029 := by
  unfold tailWord_4714584
  simp only [CollatzResearch.WordTrace]
  refine ⟨85977502575937414844055403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114636670101249886458740537 85977502575937414844055403)
  ·
    refine ⟨128966253863906122266083105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85977502575937414844055403 128966253863906122266083105)
    ·
      refine ⟨96724690397929591699562329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128966253863906122266083105 96724690397929591699562329)
      ·
        refine ⟨72543517798447193774671747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96724690397929591699562329 72543517798447193774671747)
        ·
          refine ⟨108815276697670790662007621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72543517798447193774671747 108815276697670790662007621)
          ·
            refine ⟨20402864380813273249126429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108815276697670790662007621 20402864380813273249126429)
            ·
              refine ⟨7651074142804977468422411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20402864380813273249126429 7651074142804977468422411)
              ·
                refine ⟨11476611214207466202633617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7651074142804977468422411 11476611214207466202633617)
                ·
                  refine ⟨8607458410655599651975213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11476611214207466202633617 8607458410655599651975213)
                  ·
                    refine ⟨3227796903995849869490705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8607458410655599651975213 3227796903995849869490705)
                    ·
                      refine ⟨2420847677996887402118029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227796903995849869490705 2420847677996887402118029)
                      ·
                        rfl

theorem cell23_4714584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_4714584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714584 prefixEnd_4714584 := by exact prefixLift 4714584
  have htrace : WordTrace (prefixWord ++ tailWord_4714584) baseStart_4714584 baseEnd_4714584 := by
    simpa [prefixWord, tailWord_4714584, baseEnd_4714584] using wordTrace_append hprefix tailTrace_4714584
  have hstable : (prefixWord ++ tailWord_4714584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714584).length < 2 ^ (prefixWord ++ tailWord_4714584).sum := by decide
  have hdescent : baseEnd_4714584 < baseStart_4714584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714607 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 4, 4]
def baseStart_4714607 : Nat := 118140960795 + 4714607 * 2 ^ 59
def prefixEnd_4714607 : Nat := 4983230072969 + 3 ^ 40 * 4714607 * 2
def baseEnd_4714607 : Nat := 806953162683980270710141

theorem tailTrace_4714607 : CollatzResearch.WordTrace tailWord_4714607 prefixEnd_4714607 806953162683980270710141 := by
  unfold tailWord_4714607
  simp only [CollatzResearch.WordTrace]
  refine ⟨171955844030791504616198075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114637229353861003077465383 171955844030791504616198075)
  ·
    refine ⟨257933766046187256924297113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171955844030791504616198075 257933766046187256924297113)
    ·
      refine ⟨193450324534640442693222835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257933766046187256924297113 193450324534640442693222835)
      ·
        refine ⟨290175486801960664039834253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193450324534640442693222835 290175486801960664039834253)
        ·
          refine ⟨108815807550735249014937845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290175486801960664039834253 108815807550735249014937845)
          ·
            refine ⟨10201481957881429595150423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108815807550735249014937845 10201481957881429595150423)
            ·
              refine ⟨15302222936822144392725635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10201481957881429595150423 15302222936822144392725635)
              ·
                refine ⟨22953334405233216589088453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15302222936822144392725635 22953334405233216589088453)
                ·
                  refine ⟨4303750200981228110454085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22953334405233216589088453 4303750200981228110454085)
                  ·
                    refine ⟨806953162683980270710141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4303750200981228110454085 806953162683980270710141)
                    ·
                      rfl

theorem cell23_4714607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_4714607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714607 prefixEnd_4714607 := by exact prefixLift 4714607
  have htrace : WordTrace (prefixWord ++ tailWord_4714607) baseStart_4714607 baseEnd_4714607 := by
    simpa [prefixWord, tailWord_4714607, baseEnd_4714607] using wordTrace_append hprefix tailTrace_4714607
  have hstable : (prefixWord ++ tailWord_4714607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714607).length < 2 ^ (prefixWord ++ tailWord_4714607).sum := by decide
  have hdescent : baseEnd_4714607 < baseStart_4714607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714617 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_4714617 : Nat := 118140960795 + 4714617 * 2 ^ 59
def prefixEnd_4714617 : Nat := 4983230072969 + 3 ^ 40 * 4714617 * 2
def baseEnd_4714617 : Nat := 2420864622858485773005377

theorem tailTrace_4714617 : CollatzResearch.WordTrace tailWord_4714617 prefixEnd_4714617 2420864622858485773005377 := by
  unfold tailWord_4714617
  simp only [CollatzResearch.WordTrace]
  refine ⟨171956208760755276324062105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114637472507170184216041403 171956208760755276324062105)
  ·
    refine ⟨128967156570566457243046579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171956208760755276324062105 128967156570566457243046579)
    ·
      refine ⟨193450734855849685864569869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128967156570566457243046579 193450734855849685864569869)
      ·
        refine ⟨72544025570943632199213701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193450734855849685864569869 72544025570943632199213701)
        ·
          refine ⟨13602004794551931037352569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72544025570943632199213701 13602004794551931037352569)
          ·
            refine ⟨10201503595913948278014427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13602004794551931037352569 10201503595913948278014427)
            ·
              refine ⟨15302255393870922417021641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10201503595913948278014427 15302255393870922417021641)
              ·
                refine ⟨11476691545403191812766231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15302255393870922417021641 11476691545403191812766231)
                ·
                  refine ⟨17215037318104787719149347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11476691545403191812766231 17215037318104787719149347)
                  ·
                    refine ⟨25822555977157181578724021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17215037318104787719149347 25822555977157181578724021)
                    ·
                      refine ⟨2420864622858485773005377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25822555977157181578724021 2420864622858485773005377)
                      ·
                        rfl

theorem cell23_4714617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_4714617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714617 prefixEnd_4714617 := by exact prefixLift 4714617
  have htrace : WordTrace (prefixWord ++ tailWord_4714617) baseStart_4714617 baseEnd_4714617 := by
    simpa [prefixWord, tailWord_4714617, baseEnd_4714617] using wordTrace_append hprefix tailTrace_4714617
  have hstable : (prefixWord ++ tailWord_4714617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714617).length < 2 ^ (prefixWord ++ tailWord_4714617).sum := by decide
  have hdescent : baseEnd_4714617 < baseStart_4714617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714627 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 4]
def baseStart_4714627 : Nat := 118140960795 + 4714627 * 2 ^ 59
def prefixEnd_4714627 : Nat := 4983230072969 + 3 ^ 40 * 4714627 * 2
def baseEnd_4714627 : Nat := 2420869757665030733880331

theorem tailTrace_4714627 : CollatzResearch.WordTrace tailWord_4714627 prefixEnd_4714627 2420869757665030733880331 := by
  unfold tailWord_4714627
  simp only [CollatzResearch.WordTrace]
  refine ⟨171956573490719048031926135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114637715660479365354617423 171956573490719048031926135)
  ·
    refine ⟨257934860236078572047889203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171956573490719048031926135 257934860236078572047889203)
    ·
      refine ⟨386902290354117858071833805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257934860236078572047889203 386902290354117858071833805)
      ·
        refine ⟨145088358882794196776937677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386902290354117858071833805 145088358882794196776937677)
        ·
          refine ⟨54408134581047823791351629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145088358882794196776937677 54408134581047823791351629)
          ·
            refine ⟨20403050467892933921756861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54408134581047823791351629 20403050467892933921756861)
            ·
              refine ⟨7651143925459850220658823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20403050467892933921756861 7651143925459850220658823)
              ·
                refine ⟨11476715888189775330988235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7651143925459850220658823 11476715888189775330988235)
                ·
                  refine ⟨17215073832284662996482353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11476715888189775330988235 17215073832284662996482353)
                  ·
                    refine ⟨12911305374213497247361765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17215073832284662996482353 12911305374213497247361765)
                    ·
                      refine ⟨2420869757665030733880331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12911305374213497247361765 2420869757665030733880331)
                      ·
                        rfl

theorem cell23_4714627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_4714627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714627 prefixEnd_4714627 := by exact prefixLift 4714627
  have htrace : WordTrace (prefixWord ++ tailWord_4714627) baseStart_4714627 baseEnd_4714627 := by
    simpa [prefixWord, tailWord_4714627, baseEnd_4714627] using wordTrace_append hprefix tailTrace_4714627
  have hstable : (prefixWord ++ tailWord_4714627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714627).length < 2 ^ (prefixWord ++ tailWord_4714627).sum := by decide
  have hdescent : baseEnd_4714627 < baseStart_4714627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714634 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_4714634 : Nat := 118140960795 + 4714634 * 2 ^ 59
def prefixEnd_4714634 : Nat := 4983230072969 + 3 ^ 40 * 4714634 * 2
def baseEnd_4714634 : Nat := 2420873352029612206492799

theorem tailTrace_4714634 : CollatzResearch.WordTrace tailWord_4714634 prefixEnd_4714634 2420873352029612206492799 := by
  unfold tailWord_4714634
  simp only [CollatzResearch.WordTrace]
  refine ⟨42989207200423422056857739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114637885867795792151620637 42989207200423422056857739)
  ·
    refine ⟨64483810800635133085286609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42989207200423422056857739 64483810800635133085286609)
    ·
      refine ⟨48362858100476349813964957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64483810800635133085286609 48362858100476349813964957)
      ·
        refine ⟨18136071787678631180236859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48362858100476349813964957 18136071787678631180236859)
        ·
          refine ⟨27204107681517946770355289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18136071787678631180236859 27204107681517946770355289)
          ·
            refine ⟨20403080761138460077766467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27204107681517946770355289 20403080761138460077766467)
            ·
              refine ⟨30604621141707690116649701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20403080761138460077766467 30604621141707690116649701)
              ·
                refine ⟨5738366464070191896871819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30604621141707690116649701 5738366464070191896871819)
                ·
                  refine ⟨8607549696105287845307729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5738366464070191896871819 8607549696105287845307729)
                  ·
                    refine ⟨6455662272078965883980797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8607549696105287845307729 6455662272078965883980797)
                    ·
                      refine ⟨2420873352029612206492799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6455662272078965883980797 2420873352029612206492799)
                      ·
                        rfl

theorem cell23_4714634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_4714634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714634 prefixEnd_4714634 := by exact prefixLift 4714634
  have htrace : WordTrace (prefixWord ++ tailWord_4714634) baseStart_4714634 baseEnd_4714634 := by
    simpa [prefixWord, tailWord_4714634, baseEnd_4714634] using wordTrace_append hprefix tailTrace_4714634
  have hstable : (prefixWord ++ tailWord_4714634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714634).length < 2 ^ (prefixWord ++ tailWord_4714634).sum := by decide
  have hdescent : baseEnd_4714634 < baseStart_4714634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714654 : List Nat := [4, 3, 1, 1, 3, 2, 9]
def baseStart_4714654 : Nat := 118140960795 + 4714654 * 2 ^ 59
def prefixEnd_4714654 : Nat := 4983230072969 + 3 ^ 40 * 4714654 * 2
def baseEnd_4714654 : Nat := 29887452119045705286947

theorem tailTrace_4714654 : CollatzResearch.WordTrace tailWord_4714654 prefixEnd_4714654 29887452119045705286947 := by
  unfold tailWord_4714654
  simp only [CollatzResearch.WordTrace]
  refine ⟨21494694782702653955394877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114638372174414154428772677 21494694782702653955394877)
  ·
    refine ⟨8060510543513495233273079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21494694782702653955394877 8060510543513495233273079)
    ·
      refine ⟨12090765815270242849909619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8060510543513495233273079 12090765815270242849909619)
      ·
        refine ⟨18136148722905364274864429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12090765815270242849909619 18136148722905364274864429)
        ·
          refine ⟨6801055771089511603074161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18136148722905364274864429 6801055771089511603074161)
          ·
            refine ⟨5100791828317133702305621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6801055771089511603074161 5100791828317133702305621)
            ·
              refine ⟨29887452119045705286947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5100791828317133702305621 29887452119045705286947)
              ·
                rfl

theorem cell23_4714654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 9].length) (baseStart_4714654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714654 prefixEnd_4714654 := by exact prefixLift 4714654
  have htrace : WordTrace (prefixWord ++ tailWord_4714654) baseStart_4714654 baseEnd_4714654 := by
    simpa [prefixWord, tailWord_4714654, baseEnd_4714654] using wordTrace_append hprefix tailTrace_4714654
  have hstable : (prefixWord ++ tailWord_4714654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714654).length < 2 ^ (prefixWord ++ tailWord_4714654).sum := by decide
  have hdescent : baseEnd_4714654 < baseStart_4714654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714674 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_4714674 : Nat := 118140960795 + 4714674 * 2 ^ 59
def prefixEnd_4714674 : Nat := 4983230072969 + 3 ^ 40 * 4714674 * 2
def baseEnd_4714674 : Nat := 2420893891255792049992615

theorem tailTrace_4714674 : CollatzResearch.WordTrace tailWord_4714674 prefixEnd_4714674 2420893891255792049992615 := by
  unfold tailWord_4714674
  simp only [CollatzResearch.WordTrace]
  refine ⟨42989571930387193764721769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114638858481032516705924717 42989571930387193764721769)
  ·
    refine ⟨32242178947790395323541327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42989571930387193764721769 32242178947790395323541327)
    ·
      refine ⟨48363268421685592985311991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32242178947790395323541327 48363268421685592985311991)
      ·
        refine ⟨72544902632528389477967987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48363268421685592985311991 72544902632528389477967987)
        ·
          refine ⟨108817353948792584216951981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72544902632528389477967987 108817353948792584216951981)
          ·
            refine ⟨40806507730797219081356993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108817353948792584216951981 40806507730797219081356993)
            ·
              refine ⟨30604880798097914311017745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40806507730797219081356993 30604880798097914311017745)
              ·
                refine ⟨22953660598573435733263309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30604880798097914311017745 22953660598573435733263309)
                ·
                  refine ⟨8607622724465038399973741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22953660598573435733263309 8607622724465038399973741)
                  ·
                    refine ⟨3227858521674389399990153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8607622724465038399973741 3227858521674389399990153)
                    ·
                      refine ⟨2420893891255792049992615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227858521674389399990153 2420893891255792049992615)
                      ·
                        rfl

theorem cell23_4714674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_4714674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714674 prefixEnd_4714674 := by exact prefixLift 4714674
  have htrace : WordTrace (prefixWord ++ tailWord_4714674) baseStart_4714674 baseEnd_4714674 := by
    simpa [prefixWord, tailWord_4714674, baseEnd_4714674] using wordTrace_append hprefix tailTrace_4714674
  have hstable : (prefixWord ++ tailWord_4714674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714674).length < 2 ^ (prefixWord ++ tailWord_4714674).sum := by decide
  have hdescent : baseEnd_4714674 < baseStart_4714674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714680 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 1, 8]
def baseStart_4714680 : Nat := 118140960795 + 4714680 * 2 ^ 59
def prefixEnd_4714680 : Nat := 4983230072969 + 3 ^ 40 * 4714680 * 2
def baseEnd_4714680 : Nat := 806965657379906342172529

theorem tailTrace_4714680 : CollatzResearch.WordTrace tailWord_4714680 prefixEnd_4714680 806965657379906342172529 := by
  unfold tailWord_4714680
  simp only [CollatzResearch.WordTrace]
  refine ⟨85979253279763519041802747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114639004373018025389070329 85979253279763519041802747)
  ·
    refine ⟨128968879919645278562704121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85979253279763519041802747 128968879919645278562704121)
    ·
      refine ⟨96726659939733958922028091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128968879919645278562704121 96726659939733958922028091)
      ·
        refine ⟨145089989909600938383042137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96726659939733958922028091 145089989909600938383042137)
        ·
          refine ⟨108817492432200703787281603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145089989909600938383042137 108817492432200703787281603)
          ·
            refine ⟨163226238648301055680922405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108817492432200703787281603 163226238648301055680922405)
            ·
              refine ⟨30604919746556447940172951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163226238648301055680922405 30604919746556447940172951)
              ·
                refine ⟨45907379619834671910259427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30604919746556447940172951 45907379619834671910259427)
                ·
                  refine ⟨68861069429752007865389141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45907379619834671910259427 68861069429752007865389141)
                  ·
                    refine ⟨806965657379906342172529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68861069429752007865389141 806965657379906342172529)
                    ·
                      rfl

theorem cell23_4714680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_4714680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714680 prefixEnd_4714680 := by exact prefixLift 4714680
  have htrace : WordTrace (prefixWord ++ tailWord_4714680) baseStart_4714680 baseEnd_4714680 := by
    simpa [prefixWord, tailWord_4714680, baseEnd_4714680] using wordTrace_append hprefix tailTrace_4714680
  have hstable : (prefixWord ++ tailWord_4714680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714680).length < 2 ^ (prefixWord ++ tailWord_4714680).sum := by decide
  have hdescent : baseEnd_4714680 < baseStart_4714680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714716 : List Nat := [2, 2, 5, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4714716 : Nat := 118140960795 + 4714716 * 2 ^ 59
def prefixEnd_4714716 : Nat := 4983230072969 + 3 ^ 40 * 4714716 * 2
def baseEnd_4714716 : Nat := 2420915457443280885667423

theorem tailTrace_4714716 : CollatzResearch.WordTrace tailWord_4714716 prefixEnd_4714716 2420915457443280885667423 := by
  unfold tailWord_4714716
  simp only [CollatzResearch.WordTrace]
  refine ⟨85979909793698308115958001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114639879724931077487944001 85979909793698308115958001)
  ·
    refine ⟨64484932345273731086968501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85979909793698308115958001 64484932345273731086968501)
    ·
      refine ⟨6045462407369412289403297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64484932345273731086968501 6045462407369412289403297)
      ·
        refine ⟨4534096805527059217052473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6045462407369412289403297 4534096805527059217052473)
        ·
          refine ⟨3400572604145294412789355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4534096805527059217052473 3400572604145294412789355)
          ·
            refine ⟨5100858906217941619184033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400572604145294412789355 5100858906217941619184033)
            ·
              refine ⟨3825644179663456214388025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5100858906217941619184033 3825644179663456214388025)
              ·
                refine ⟨2869233134747592160791019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825644179663456214388025 2869233134747592160791019)
                ·
                  refine ⟨4303849702121388241186529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869233134747592160791019 4303849702121388241186529)
                  ·
                    refine ⟨3227887276591041180889897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4303849702121388241186529 3227887276591041180889897)
                    ·
                      refine ⟨2420915457443280885667423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227887276591041180889897 2420915457443280885667423)
                      ·
                        rfl

theorem cell23_4714716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4714716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714716 prefixEnd_4714716 := by exact prefixLift 4714716
  have htrace : WordTrace (prefixWord ++ tailWord_4714716) baseStart_4714716 baseEnd_4714716 := by
    simpa [prefixWord, tailWord_4714716, baseEnd_4714716] using wordTrace_append hprefix tailTrace_4714716
  have hstable : (prefixWord ++ tailWord_4714716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714716).length < 2 ^ (prefixWord ++ tailWord_4714716).sum := by decide
  have hdescent : baseEnd_4714716 < baseStart_4714716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714737 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_4714737 : Nat := 118140960795 + 4714737 * 2 ^ 59
def prefixEnd_4714737 : Nat := 4983230072969 + 3 ^ 40 * 4714737 * 2
def baseEnd_4714737 : Nat := 2420926240537025303504825

theorem tailTrace_4714737 : CollatzResearch.WordTrace tailWord_4714737 prefixEnd_4714737 2420926240537025303504825 := by
  unfold tailWord_4714737
  simp only [CollatzResearch.WordTrace]
  refine ⟨171960585520320536818430465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114640390346880357878953643 171960585520320536818430465)
  ·
    refine ⟨128970439140240402613822849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171960585520320536818430465 128970439140240402613822849)
    ·
      refine ⟨96727829355180301960367137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128970439140240402613822849 96727829355180301960367137)
      ·
        refine ⟨72545872016385226470275353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96727829355180301960367137 72545872016385226470275353)
        ·
          refine ⟨54409404012288919852706515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72545872016385226470275353 54409404012288919852706515)
          ·
            refine ⟨81614106018433379779059773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54409404012288919852706515 81614106018433379779059773)
            ·
              refine ⟨30605289756912517417147415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81614106018433379779059773 30605289756912517417147415)
              ·
                refine ⟨45907934635368776125721123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30605289756912517417147415 45907934635368776125721123)
                ·
                  refine ⟨68861901953053164188581685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45907934635368776125721123 68861901953053164188581685)
                  ·
                    refine ⟨6455803308098734142679533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68861901953053164188581685 6455803308098734142679533)
                    ·
                      refine ⟨2420926240537025303504825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6455803308098734142679533 2420926240537025303504825)
                      ·
                        rfl

theorem cell23_4714737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_4714737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714737 prefixEnd_4714737 := by exact prefixLift 4714737
  have htrace : WordTrace (prefixWord ++ tailWord_4714737) baseStart_4714737 baseEnd_4714737 := by
    simpa [prefixWord, tailWord_4714737, baseEnd_4714737] using wordTrace_append hprefix tailTrace_4714737
  have hstable : (prefixWord ++ tailWord_4714737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714737).length < 2 ^ (prefixWord ++ tailWord_4714737).sum := by decide
  have hdescent : baseEnd_4714737 < baseStart_4714737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714738 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_4714738 : Nat := 118140960795 + 4714738 * 2 ^ 59
def prefixEnd_4714738 : Nat := 4983230072969 + 3 ^ 40 * 4714738 * 2
def baseEnd_4714738 : Nat := 2420926754017679799592321

theorem tailTrace_4714738 : CollatzResearch.WordTrace tailWord_4714738 prefixEnd_4714738 2420926754017679799592321 := by
  unfold tailWord_4714738
  simp only [CollatzResearch.WordTrace]
  refine ⟨42990155498329228497304217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114640414662211275992811245 42990155498329228497304217)
  ·
    refine ⟨32242616623746921372978163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42990155498329228497304217 32242616623746921372978163)
    ·
      refine ⟨48363924935620382059467245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32242616623746921372978163 48363924935620382059467245)
      ·
        refine ⟨18136471850857643272300217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48363924935620382059467245 18136471850857643272300217)
        ·
          refine ⟨13602353888143232454225163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18136471850857643272300217 13602353888143232454225163)
          ·
            refine ⟨20403530832214848681337745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13602353888143232454225163 20403530832214848681337745)
            ·
              refine ⟨15302648124161136511003309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20403530832214848681337745 15302648124161136511003309)
              ·
                refine ⟨5738493046560426191626241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15302648124161136511003309 5738493046560426191626241)
                ·
                  refine ⟨4303869784920319643719681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5738493046560426191626241 4303869784920319643719681)
                  ·
                    refine ⟨3227902338690239732789761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4303869784920319643719681 3227902338690239732789761)
                    ·
                      refine ⟨2420926754017679799592321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3227902338690239732789761 2420926754017679799592321)
                      ·
                        rfl

theorem cell23_4714738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_4714738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714738 prefixEnd_4714738 := by exact prefixLift 4714738
  have htrace : WordTrace (prefixWord ++ tailWord_4714738) baseStart_4714738 baseEnd_4714738 := by
    simpa [prefixWord, tailWord_4714738, baseEnd_4714738] using wordTrace_append hprefix tailTrace_4714738
  have hstable : (prefixWord ++ tailWord_4714738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714738).length < 2 ^ (prefixWord ++ tailWord_4714738).sum := by decide
  have hdescent : baseEnd_4714738 < baseStart_4714738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714757 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_4714757 : Nat := 118140960795 + 4714757 * 2 ^ 59
def prefixEnd_4714757 : Nat := 4983230072969 + 3 ^ 40 * 4714757 * 2
def baseEnd_4714757 : Nat := 806978836716705075084911

theorem tailTrace_4714757 : CollatzResearch.WordTrace tailWord_4714757 prefixEnd_4714757 806978836716705075084911 := by
  unfold tailWord_4714757
  simp only [CollatzResearch.WordTrace]
  refine ⟨171961314980248080234158525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114640876653498720156105683 171961314980248080234158525)
  ·
    refine ⟨64485493117593030087809447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171961314980248080234158525 64485493117593030087809447)
    ·
      refine ⟨96728239676389545131714171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64485493117593030087809447 96728239676389545131714171)
      ·
        refine ⟨145092359514584317697571257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96728239676389545131714171 145092359514584317697571257)
        ·
          refine ⟨108819269635938238273178443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145092359514584317697571257 108819269635938238273178443)
          ·
            refine ⟨163228904453907357409767665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108819269635938238273178443 163228904453907357409767665)
            ·
              refine ⟨122421678340430518057325749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163228904453907357409767665 122421678340430518057325749)
              ·
                refine ⟨11477032344415361067874289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122421678340430518057325749 11477032344415361067874289)
                ·
                  refine ⟨8607774258311520800905717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11477032344415361067874289 8607774258311520800905717)
                  ·
                    refine ⟨806978836716705075084911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8607774258311520800905717 806978836716705075084911)
                    ·
                      rfl

theorem cell23_4714757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_4714757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714757 prefixEnd_4714757 := by exact prefixLift 4714757
  have htrace : WordTrace (prefixWord ++ tailWord_4714757) baseStart_4714757 baseEnd_4714757 := by
    simpa [prefixWord, tailWord_4714757, baseEnd_4714757] using wordTrace_append hprefix tailTrace_4714757
  have hstable : (prefixWord ++ tailWord_4714757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714757).length < 2 ^ (prefixWord ++ tailWord_4714757).sum := by decide
  have hdescent : baseEnd_4714757 < baseStart_4714757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714861 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_4714861 : Nat := 118140960795 + 4714861 * 2 ^ 59
def prefixEnd_4714861 : Nat := 4983230072969 + 3 ^ 40 * 4714861 * 2
def baseEnd_4714861 : Nat := 2420989912138182818354255

theorem tailTrace_4714861 : CollatzResearch.WordTrace tailWord_4714861 prefixEnd_4714861 2420989912138182818354255 := by
  unfold tailWord_4714861
  simp only [CollatzResearch.WordTrace]
  refine ⟨171965108171871305995944437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114643405447914203997296291 171965108171871305995944437)
  ·
    refine ⟨16121728891112934937119791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171965108171871305995944437 16121728891112934937119791)
    ·
      refine ⟨24182593336669402405679687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16121728891112934937119791 24182593336669402405679687)
      ·
        refine ⟨36273890005004103608519531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24182593336669402405679687 36273890005004103608519531)
        ·
          refine ⟨54410835007506155412779297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36273890005004103608519531 54410835007506155412779297)
          ·
            refine ⟨40808126255629616559584473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54410835007506155412779297 40808126255629616559584473)
            ·
              refine ⟨30606094691722212419688355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40808126255629616559584473 30606094691722212419688355)
              ·
                refine ⟨45909142037583318629532533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30606094691722212419688355 45909142037583318629532533)
                ·
                  refine ⟨4303982066023436121518675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45909142037583318629532533 4303982066023436121518675)
                  ·
                    refine ⟨6455973099035154182278013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4303982066023436121518675 6455973099035154182278013)
                    ·
                      refine ⟨2420989912138182818354255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6455973099035154182278013 2420989912138182818354255)
                      ·
                        rfl

theorem cell23_4714861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_4714861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714861 prefixEnd_4714861 := by exact prefixLift 4714861
  have htrace : WordTrace (prefixWord ++ tailWord_4714861) baseStart_4714861 baseEnd_4714861 := by
    simpa [prefixWord, tailWord_4714861, baseEnd_4714861] using wordTrace_append hprefix tailTrace_4714861
  have hstable : (prefixWord ++ tailWord_4714861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714861).length < 2 ^ (prefixWord ++ tailWord_4714861).sum := by decide
  have hdescent : baseEnd_4714861 < baseStart_4714861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714864 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 3, 5]
def baseStart_4714864 : Nat := 118140960795 + 4714864 * 2 ^ 59
def prefixEnd_4714864 : Nat := 4983230072969 + 3 ^ 40 * 4714864 * 2
def baseEnd_4714864 : Nat := 806997150860048768872247

theorem tailTrace_4714864 : CollatzResearch.WordTrace tailWord_4714864 prefixEnd_4714864 806997150860048768872247 := by
  unfold tailWord_4714864
  simp only [CollatzResearch.WordTrace]
  refine ⟨85982608795430218754151823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114643478393906958338869097 85982608795430218754151823)
  ·
    refine ⟨128973913193145328131227735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85982608795430218754151823 128973913193145328131227735)
    ·
      refine ⟨193460869789717992196841603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128973913193145328131227735 193460869789717992196841603)
      ·
        refine ⟨290191304684576988295262405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193460869789717992196841603 290191304684576988295262405)
        ·
          refine ⟨54410869628358185305361701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290191304684576988295262405 54410869628358185305361701)
          ·
            refine ⟨10202038055317159744755319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54410869628358185305361701 10202038055317159744755319)
            ·
              refine ⟨15303057082975739617132979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10202038055317159744755319 15303057082975739617132979)
              ·
                refine ⟨22954585624463609425699469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15303057082975739617132979 22954585624463609425699469)
                ·
                  refine ⟨8607969609173853534637301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22954585624463609425699469 8607969609173853534637301)
                  ·
                    refine ⟨806997150860048768872247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8607969609173853534637301 806997150860048768872247)
                    ·
                      rfl

theorem cell23_4714864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_4714864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714864 prefixEnd_4714864 := by exact prefixLift 4714864
  have htrace : WordTrace (prefixWord ++ tailWord_4714864) baseStart_4714864 baseEnd_4714864 := by
    simpa [prefixWord, tailWord_4714864, baseEnd_4714864] using wordTrace_append hprefix tailTrace_4714864
  have hstable : (prefixWord ++ tailWord_4714864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714864).length < 2 ^ (prefixWord ++ tailWord_4714864).sum := by decide
  have hdescent : baseEnd_4714864 < baseStart_4714864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714867 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4]
def baseStart_4714867 : Nat := 118140960795 + 4714867 * 2 ^ 59
def prefixEnd_4714867 : Nat := 4983230072969 + 3 ^ 40 * 4714867 * 2
def baseEnd_4714867 : Nat := 2420992993022109794879227

theorem tailTrace_4714867 : CollatzResearch.WordTrace tailWord_4714867 prefixEnd_4714867 2420992993022109794879227 := by
  unfold tailWord_4714867
  simp only [CollatzResearch.WordTrace]
  refine ⟨171965327009849569020662855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114643551339899712680441903 171965327009849569020662855)
  ·
    refine ⟨257947990514774353530994283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171965327009849569020662855 257947990514774353530994283)
    ·
      refine ⟨386921985772161530296491425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257947990514774353530994283 386921985772161530296491425)
      ·
        refine ⟨290191489329121147722368569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386921985772161530296491425 290191489329121147722368569)
        ·
          refine ⟨217643616996840860791776427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290191489329121147722368569 217643616996840860791776427)
          ·
            refine ⟨326465425495261291187664641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217643616996840860791776427 326465425495261291187664641)
            ·
              refine ⟨244849069121445968390748481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326465425495261291187664641 244849069121445968390748481)
              ·
                refine ⟨183636801841084476293061361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244849069121445968390748481 183636801841084476293061361)
                ·
                  refine ⟨137727601380813357219796021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183636801841084476293061361 137727601380813357219796021)
                  ·
                    refine ⟨12911962629451252239355877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137727601380813357219796021 12911962629451252239355877)
                    ·
                      refine ⟨2420992993022109794879227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12911962629451252239355877 2420992993022109794879227)
                      ·
                        rfl

theorem cell23_4714867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_4714867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714867 prefixEnd_4714867 := by exact prefixLift 4714867
  have htrace : WordTrace (prefixWord ++ tailWord_4714867) baseStart_4714867 baseEnd_4714867 := by
    simpa [prefixWord, tailWord_4714867, baseEnd_4714867] using wordTrace_append hprefix tailTrace_4714867
  have hstable : (prefixWord ++ tailWord_4714867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714867).length < 2 ^ (prefixWord ++ tailWord_4714867).sum := by decide
  have hdescent : baseEnd_4714867 < baseStart_4714867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714911 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 2, 4]
def baseStart_4714911 : Nat := 118140960795 + 4714911 * 2 ^ 59
def prefixEnd_4714911 : Nat := 4983230072969 + 3 ^ 40 * 4714911 * 2
def baseEnd_4714911 : Nat := 807005195390302540909675

theorem tailTrace_4714911 : CollatzResearch.WordTrace tailWord_4714911 prefixEnd_4714911 807005195390302540909675 := by
  unfold tailWord_4714911
  simp only [CollatzResearch.WordTrace]
  refine ⟨171966931821690164535264587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114644621214460109690176391 171966931821690164535264587)
  ·
    refine ⟨257950397732535246802896881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171966931821690164535264587 257950397732535246802896881)
    ·
      refine ⟨193462798299401435102172661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257950397732535246802896881 193462798299401435102172661)
      ·
        refine ⟨18137137340568884540828687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193462798299401435102172661 18137137340568884540828687)
        ·
          refine ⟨27205706010853326811243031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18137137340568884540828687 27205706010853326811243031)
          ·
            refine ⟨40808559016279990216864547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27205706010853326811243031 40808559016279990216864547)
            ·
              refine ⟨61212838524419985325296821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40808559016279990216864547 61212838524419985325296821)
              ·
                refine ⟨5738703611664373624246577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61212838524419985325296821 5738703611664373624246577)
                ·
                  refine ⟨4304027708748280218184933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5738703611664373624246577 4304027708748280218184933)
                  ·
                    refine ⟨807005195390302540909675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304027708748280218184933 807005195390302540909675)
                    ·
                      rfl

theorem cell23_4714911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_4714911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714911 prefixEnd_4714911 := by exact prefixLift 4714911
  have htrace : WordTrace (prefixWord ++ tailWord_4714911) baseStart_4714911 baseEnd_4714911 := by
    simpa [prefixWord, tailWord_4714911, baseEnd_4714911] using wordTrace_append hprefix tailTrace_4714911
  have hstable : (prefixWord ++ tailWord_4714911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714911).length < 2 ^ (prefixWord ++ tailWord_4714911).sum := by decide
  have hdescent : baseEnd_4714911 < baseStart_4714911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714922 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4714922 : Nat := 118140960795 + 4714922 * 2 ^ 59
def prefixEnd_4714922 : Nat := 4983230072969 + 3 ^ 40 * 4714922 * 2
def baseEnd_4714922 : Nat := 2421021234458107079691475

theorem tailTrace_4714922 : CollatzResearch.WordTrace tailWord_4714922 prefixEnd_4714922 2421021234458107079691475 := by
  unfold tailWord_4714922
  simp only [CollatzResearch.WordTrace]
  refine ⟨42991833256162578353478755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114644888683100208942610013 42991833256162578353478755)
  ·
    refine ⟨64487749884243867530218133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42991833256162578353478755 64487749884243867530218133)
    ·
      refine ⟨3022863275823931290478975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64487749884243867530218133 3022863275823931290478975)
      ·
        refine ⟨4534294913735896935718463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3022863275823931290478975 4534294913735896935718463)
        ·
          refine ⟨6801442370603845403577695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534294913735896935718463 6801442370603845403577695)
          ·
            refine ⟨10202163555905768105366543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6801442370603845403577695 10202163555905768105366543)
            ·
              refine ⟨15303245333858652158049815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10202163555905768105366543 15303245333858652158049815)
              ·
                refine ⟨22954868000787978237074723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15303245333858652158049815 22954868000787978237074723)
                ·
                  refine ⟨34432302001181967355612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22954868000787978237074723 34432302001181967355612085)
                  ·
                    refine ⟨3228028312610809439588633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34432302001181967355612085 3228028312610809439588633)
                    ·
                      refine ⟨2421021234458107079691475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228028312610809439588633 2421021234458107079691475)
                      ·
                        rfl

theorem cell23_4714922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4714922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714922 prefixEnd_4714922 := by exact prefixLift 4714922
  have htrace : WordTrace (prefixWord ++ tailWord_4714922) baseStart_4714922 baseEnd_4714922 := by
    simpa [prefixWord, tailWord_4714922, baseEnd_4714922] using wordTrace_append hprefix tailTrace_4714922
  have hstable : (prefixWord ++ tailWord_4714922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714922).length < 2 ^ (prefixWord ++ tailWord_4714922).sum := by decide
  have hdescent : baseEnd_4714922 < baseStart_4714922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714935 : List Nat := [1, 1, 3, 1, 3, 3, 1, 5, 1, 2, 2]
def baseStart_4714935 : Nat := 118140960795 + 4714935 * 2 ^ 59
def prefixEnd_4714935 : Nat := 4983230072969 + 3 ^ 40 * 4714935 * 2
def baseEnd_4714935 : Nat := 2421027909706615528828915

theorem tailTrace_4714935 : CollatzResearch.WordTrace tailWord_4714935 prefixEnd_4714935 2421027909706615528828915 := by
  unfold tailWord_4714935
  simp only [CollatzResearch.WordTrace]
  refine ⟨171967807173603216634138259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114645204782402144422758839 171967807173603216634138259)
  ·
    refine ⟨257951710760404824951207389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171967807173603216634138259 257951710760404824951207389)
    ·
      refine ⟨96731891535151809356702771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257951710760404824951207389 96731891535151809356702771)
      ·
        refine ⟨145097837302727714035054157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96731891535151809356702771 145097837302727714035054157)
        ·
          refine ⟨54411688988522892763145309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145097837302727714035054157 54411688988522892763145309)
          ·
            refine ⟨20404383370696084786179491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54411688988522892763145309 20404383370696084786179491)
            ·
              refine ⟨30606575056044127179269237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20404383370696084786179491 30606575056044127179269237)
              ·
                refine ⟨2869366411504136923056491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30606575056044127179269237 2869366411504136923056491)
                ·
                  refine ⟨4304049617256205384584737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869366411504136923056491 4304049617256205384584737)
                  ·
                    refine ⟨3228037212942154038438553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4304049617256205384584737 3228037212942154038438553)
                    ·
                      refine ⟨2421027909706615528828915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228037212942154038438553 2421027909706615528828915)
                      ·
                        rfl

theorem cell23_4714935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_4714935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714935 prefixEnd_4714935 := by exact prefixLift 4714935
  have htrace : WordTrace (prefixWord ++ tailWord_4714935) baseStart_4714935 baseEnd_4714935 := by
    simpa [prefixWord, tailWord_4714935, baseEnd_4714935] using wordTrace_append hprefix tailTrace_4714935
  have hstable : (prefixWord ++ tailWord_4714935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714935).length < 2 ^ (prefixWord ++ tailWord_4714935).sum := by decide
  have hdescent : baseEnd_4714935 < baseStart_4714935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714961 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 5, 3, 2]
def baseStart_4714961 : Nat := 118140960795 + 4714961 * 2 ^ 59
def prefixEnd_4714961 : Nat := 4983230072969 + 3 ^ 40 * 4714961 * 2
def baseEnd_4714961 : Nat := 2421041260203632427103795

theorem tailTrace_4714961 : CollatzResearch.WordTrace tailWord_4714961 prefixEnd_4714961 2421041260203632427103795 := by
  unfold tailWord_4714961
  simp only [CollatzResearch.WordTrace]
  refine ⟨171968755471509023074584737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114645836981006015383056491 171968755471509023074584737)
  ·
    refine ⟨128976566603631767305938553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171968755471509023074584737 128976566603631767305938553)
    ·
      refine ⟨96732424952723825479453915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128976566603631767305938553 96732424952723825479453915)
      ·
        refine ⟨145098637429085738219180873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96732424952723825479453915 145098637429085738219180873)
        ·
          refine ⟨108823978071814303664385655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145098637429085738219180873 108823978071814303664385655)
          ·
            refine ⟨163235967107721455496578483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108823978071814303664385655 163235967107721455496578483)
            ·
              refine ⟨244853950661582183244867725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163235967107721455496578483 244853950661582183244867725)
              ·
                refine ⟨91820231498093318716825397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244853950661582183244867725 91820231498093318716825397)
                ·
                  refine ⟨8608146702946248629702381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91820231498093318716825397 8608146702946248629702381)
                  ·
                    refine ⟨3228055013604843236138393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8608146702946248629702381 3228055013604843236138393)
                    ·
                      refine ⟨2421041260203632427103795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228055013604843236138393 2421041260203632427103795)
                      ·
                        rfl

theorem cell23_4714961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_4714961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714961 prefixEnd_4714961 := by exact prefixLift 4714961
  have htrace : WordTrace (prefixWord ++ tailWord_4714961) baseStart_4714961 baseEnd_4714961 := by
    simpa [prefixWord, tailWord_4714961, baseEnd_4714961] using wordTrace_append hprefix tailTrace_4714961
  have hstable : (prefixWord ++ tailWord_4714961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714961).length < 2 ^ (prefixWord ++ tailWord_4714961).sum := by decide
  have hdescent : baseEnd_4714961 < baseStart_4714961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714962 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_4714962 : Nat := 118140960795 + 4714962 * 2 ^ 59
def prefixEnd_4714962 : Nat := 4983230072969 + 3 ^ 40 * 4714962 * 2
def baseEnd_4714962 : Nat := 807013924561428974397097

theorem tailTrace_4714962 : CollatzResearch.WordTrace tailWord_4714962 prefixEnd_4714962 807013924561428974397097 := by
  unfold tailWord_4714962
  simp only [CollatzResearch.WordTrace]
  refine ⟨42992197986126350061342785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114645861296336933496914093 42992197986126350061342785)
  ·
    refine ⟨32244148489594762546007089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42992197986126350061342785 32244148489594762546007089)
    ·
      refine ⟨24183111367196071909505317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32244148489594762546007089 24183111367196071909505317)
      ·
        refine ⟨4534333381349263483032247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24183111367196071909505317 4534333381349263483032247)
        ·
          refine ⟨6801500072023895224548371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534333381349263483032247 6801500072023895224548371)
          ·
            refine ⟨10202250108035842836822557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6801500072023895224548371 10202250108035842836822557)
            ·
              refine ⟨3825843790513441063808459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10202250108035842836822557 3825843790513441063808459)
              ·
                refine ⟨5738765685770161595712689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825843790513441063808459 5738765685770161595712689)
                ·
                  refine ⟨4304074264327621196784517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5738765685770161595712689 4304074264327621196784517)
                  ·
                    refine ⟨807013924561428974397097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304074264327621196784517 807013924561428974397097)
                    ·
                      rfl

theorem cell23_4714962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_4714962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714962 prefixEnd_4714962 := by exact prefixLift 4714962
  have htrace : WordTrace (prefixWord ++ tailWord_4714962) baseStart_4714962 baseEnd_4714962 := by
    simpa [prefixWord, tailWord_4714962, baseEnd_4714962] using wordTrace_append hprefix tailTrace_4714962
  have hstable : (prefixWord ++ tailWord_4714962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714962).length < 2 ^ (prefixWord ++ tailWord_4714962).sum := by decide
  have hdescent : baseEnd_4714962 < baseStart_4714962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4714991 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 3, 4, 2]
def baseStart_4714991 : Nat := 118140960795 + 4714991 * 2 ^ 59
def prefixEnd_4714991 : Nat := 4983230072969 + 3 ^ 40 * 4714991 * 2
def baseEnd_4714991 : Nat := 2421056664623267309728657

theorem tailTrace_4714991 : CollatzResearch.WordTrace tailWord_4714991 prefixEnd_4714991 2421056664623267309728657 := by
  unfold tailWord_4714991
  simp only [CollatzResearch.WordTrace]
  refine ⟨171969849661400338198176827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114646566440933558798784551 171969849661400338198176827)
  ·
    refine ⟨257954774492100507297265241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171969849661400338198176827 257954774492100507297265241)
    ·
      refine ⟨193466080869075380472948931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257954774492100507297265241 193466080869075380472948931)
      ·
        refine ⟨290199121303613070709423397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193466080869075380472948931 290199121303613070709423397)
        ·
          refine ⟨54412335244427450758016887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290199121303613070709423397 54412335244427450758016887)
          ·
            refine ⟨81618502866641176137025331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54412335244427450758016887 81618502866641176137025331)
            ·
              refine ⟨122427754299961764205537997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81618502866641176137025331 122427754299961764205537997)
              ·
                refine ⟨45910407862485661577076749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122427754299961764205537997 45910407862485661577076749)
                ·
                  refine ⟨17216402948432123091403781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45910407862485661577076749 17216402948432123091403781)
                  ·
                    refine ⟨3228075552831023079638209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17216402948432123091403781 3228075552831023079638209)
                    ·
                      refine ⟨2421056664623267309728657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228075552831023079638209 2421056664623267309728657)
                      ·
                        rfl

theorem cell23_4714991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4, 2].length) (baseStart_4714991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4714991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4714991 prefixEnd_4714991 := by exact prefixLift 4714991
  have htrace : WordTrace (prefixWord ++ tailWord_4714991) baseStart_4714991 baseEnd_4714991 := by
    simpa [prefixWord, tailWord_4714991, baseEnd_4714991] using wordTrace_append hprefix tailTrace_4714991
  have hstable : (prefixWord ++ tailWord_4714991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4714991).length < 2 ^ (prefixWord ++ tailWord_4714991).sum := by decide
  have hdescent : baseEnd_4714991 < baseStart_4714991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4714991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715028 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4715028 : Nat := 118140960795 + 4715028 * 2 ^ 59
def prefixEnd_4715028 : Nat := 4983230072969 + 3 ^ 40 * 4715028 * 2
def baseEnd_4715028 : Nat := 2421075663407483664965987

theorem tailTrace_4715028 : CollatzResearch.WordTrace tailWord_4715028 prefixEnd_4715028 2421075663407483664965987 := by
  unfold tailWord_4715028
  simp only [CollatzResearch.WordTrace]
  refine ⟨85985599581133146758636869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114647466108177529011515825 85985599581133146758636869)
  ·
    refine ⟨16122299921462465017244413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85985599581133146758636869 16122299921462465017244413)
    ·
      refine ⟨6045862470548424381466655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16122299921462465017244413 6045862470548424381466655)
      ·
        refine ⟨9068793705822636572199983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6045862470548424381466655 9068793705822636572199983)
        ·
          refine ⟨13603190558733954858299975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9068793705822636572199983 13603190558733954858299975)
          ·
            refine ⟨20404785838100932287449963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13603190558733954858299975 20404785838100932287449963)
            ·
              refine ⟨30607178757151398431174945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20404785838100932287449963 30607178757151398431174945)
              ·
                refine ⟨22955384067863548823381209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30607178757151398431174945 22955384067863548823381209)
                ·
                  refine ⟨17216538050897661617535907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22955384067863548823381209 17216538050897661617535907)
                  ·
                    refine ⟨25824807076346492426303861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17216538050897661617535907 25824807076346492426303861)
                    ·
                      refine ⟨2421075663407483664965987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25824807076346492426303861 2421075663407483664965987)
                      ·
                        rfl

theorem cell23_4715028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4715028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715028 prefixEnd_4715028 := by exact prefixLift 4715028
  have htrace : WordTrace (prefixWord ++ tailWord_4715028) baseStart_4715028 baseEnd_4715028 := by
    simpa [prefixWord, tailWord_4715028, baseEnd_4715028] using wordTrace_append hprefix tailTrace_4715028
  have hstable : (prefixWord ++ tailWord_4715028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715028).length < 2 ^ (prefixWord ++ tailWord_4715028).sum := by decide
  have hdescent : baseEnd_4715028 < baseStart_4715028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715051 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 4, 5, 2]
def baseStart_4715051 : Nat := 118140960795 + 4715051 * 2 ^ 59
def prefixEnd_4715051 : Nat := 4983230072969 + 3 ^ 40 * 4715051 * 2
def baseEnd_4715051 : Nat := 2421087473462537074978381

theorem tailTrace_4715051 : CollatzResearch.WordTrace tailWord_4715051 prefixEnd_4715051 2421087473462537074978381 := by
  unfold tailWord_4715051
  simp only [CollatzResearch.WordTrace]
  refine ⟨171972038041182968445361007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114648025360788645630240671 171972038041182968445361007)
  ·
    refine ⟨257958057061774452668041511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171972038041182968445361007 257958057061774452668041511)
    ·
      refine ⟨386937085592661679002062267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257958057061774452668041511 386937085592661679002062267)
      ·
        refine ⟨580405628388992518503093401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386937085592661679002062267 580405628388992518503093401)
        ·
          refine ⟨435304221291744388877320051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580405628388992518503093401 435304221291744388877320051)
          ·
            refine ⟨652956331937616583315980077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435304221291744388877320051 652956331937616583315980077)
            ·
              refine ⟨244858624476606218743492529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 652956331937616583315980077 244858624476606218743492529)
              ·
                refine ⟨183643968357454664057619397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244858624476606218743492529 183643968357454664057619397)
                ·
                  refine ⟨34433244067022749510803637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183643968357454664057619397 34433244067022749510803637)
                  ·
                    refine ⟨3228116631283382766637841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34433244067022749510803637 3228116631283382766637841)
                    ·
                      refine ⟨2421087473462537074978381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228116631283382766637841 2421087473462537074978381)
                      ·
                        rfl

theorem cell23_4715051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5, 2].length) (baseStart_4715051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715051 prefixEnd_4715051 := by exact prefixLift 4715051
  have htrace : WordTrace (prefixWord ++ tailWord_4715051) baseStart_4715051 baseEnd_4715051 := by
    simpa [prefixWord, tailWord_4715051, baseEnd_4715051] using wordTrace_append hprefix tailTrace_4715051
  have hstable : (prefixWord ++ tailWord_4715051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715051).length < 2 ^ (prefixWord ++ tailWord_4715051).sum := by decide
  have hdescent : baseEnd_4715051 < baseStart_4715051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715061 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4715061 : Nat := 118140960795 + 4715061 * 2 ^ 59
def prefixEnd_4715061 : Nat := 4983230072969 + 3 ^ 40 * 4715061 * 2
def baseEnd_4715061 : Nat := 807030869423027345284445

theorem tailTrace_4715061 : CollatzResearch.WordTrace tailWord_4715061 prefixEnd_4715061 807030869423027345284445 := by
  unfold tailWord_4715061
  simp only [CollatzResearch.WordTrace]
  refine ⟨171972402771146740153225037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114648268514097826768816691 171972402771146740153225037)
  ·
    refine ⟨64489651039180027557459389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171972402771146740153225037 64489651039180027557459389)
    ·
      refine ⟨24183619139692510334047271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64489651039180027557459389 24183619139692510334047271)
      ·
        refine ⟨36275428709538765501070907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24183619139692510334047271 36275428709538765501070907)
        ·
          refine ⟨54413143064308148251606361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36275428709538765501070907 54413143064308148251606361)
          ·
            refine ⟨40809857298231111188704771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54413143064308148251606361 40809857298231111188704771)
            ·
              refine ⟨61214785947346666783057157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40809857298231111188704771 61214785947346666783057157)
              ·
                refine ⟨11477772365127500021823217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61214785947346666783057157 11477772365127500021823217)
                ·
                  refine ⟨8608329273845625016367413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11477772365127500021823217 8608329273845625016367413)
                  ·
                    refine ⟨807030869423027345284445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8608329273845625016367413 807030869423027345284445)
                    ·
                      rfl

theorem cell23_4715061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4715061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715061 prefixEnd_4715061 := by exact prefixLift 4715061
  have htrace : WordTrace (prefixWord ++ tailWord_4715061) baseStart_4715061 baseEnd_4715061 := by
    simpa [prefixWord, tailWord_4715061, baseEnd_4715061] using wordTrace_append hprefix tailTrace_4715061
  have hstable : (prefixWord ++ tailWord_4715061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715061).length < 2 ^ (prefixWord ++ tailWord_4715061).sum := by decide
  have hdescent : baseEnd_4715061 < baseStart_4715061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715068 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_4715068 : Nat := 118140960795 + 4715068 * 2 ^ 59
def prefixEnd_4715068 : Nat := 4983230072969 + 3 ^ 40 * 4715068 * 2
def baseEnd_4715068 : Nat := 2421096202633663508465803

theorem tailTrace_4715068 : CollatzResearch.WordTrace tailWord_4715068 prefixEnd_4715068 2421096202633663508465803 := by
  unfold tailWord_4715068
  simp only [CollatzResearch.WordTrace]
  refine ⟨85986329041060690174364929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114648438721414253565819905 85986329041060690174364929)
  ·
    refine ⟨64489746780795517630773697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85986329041060690174364929 64489746780795517630773697)
    ·
      refine ⟨48367310085596638223080273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64489746780795517630773697 48367310085596638223080273)
      ·
        refine ⟨36275482564197478667310205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48367310085596638223080273 36275482564197478667310205)
        ·
          refine ⟨13603305961574054500241327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36275482564197478667310205 13603305961574054500241327)
          ·
            refine ⟨20404958942361081750361991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13603305961574054500241327 20404958942361081750361991)
            ·
              refine ⟨30607438413541622625542987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20404958942361081750361991 30607438413541622625542987)
              ·
                refine ⟨45911157620312433938314481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30607438413541622625542987 45911157620312433938314481)
                ·
                  refine ⟨34433368215234325453735861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45911157620312433938314481 34433368215234325453735861)
                  ·
                    refine ⟨3228128270178218011287737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34433368215234325453735861 3228128270178218011287737)
                    ·
                      refine ⟨2421096202633663508465803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228128270178218011287737 2421096202633663508465803)
                      ·
                        rfl

theorem cell23_4715068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_4715068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715068 prefixEnd_4715068 := by exact prefixLift 4715068
  have htrace : WordTrace (prefixWord ++ tailWord_4715068) baseStart_4715068 baseEnd_4715068 := by
    simpa [prefixWord, tailWord_4715068, baseEnd_4715068] using wordTrace_append hprefix tailTrace_4715068
  have hstable : (prefixWord ++ tailWord_4715068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715068).length < 2 ^ (prefixWord ++ tailWord_4715068).sum := by decide
  have hdescent : baseEnd_4715068 < baseStart_4715068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715148 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_4715148 : Nat := 118140960795 + 4715148 * 2 ^ 59
def prefixEnd_4715148 : Nat := 4983230072969 + 3 ^ 40 * 4715148 * 2
def baseEnd_4715148 : Nat := 2421137281086023195465435

theorem tailTrace_4715148 : CollatzResearch.WordTrace tailWord_4715148 prefixEnd_4715148 2421137281086023195465435 := by
  unfold tailWord_4715148
  simp only [CollatzResearch.WordTrace]
  refine ⟨85987787960915777005821049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114650383947887702674428065 85987787960915777005821049)
  ·
    refine ⟨64490840970686832754365787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85987787960915777005821049 64490840970686832754365787)
    ·
      refine ⟨96736261456030249131548681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64490840970686832754365787 96736261456030249131548681)
      ·
        refine ⟨72552196092022686848661511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96736261456030249131548681 72552196092022686848661511)
        ·
          refine ⟨108828294138034030272992267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72552196092022686848661511 108828294138034030272992267)
          ·
            refine ⟨163242441207051045409488401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108828294138034030272992267 163242441207051045409488401)
            ·
              refine ⟨122431830905288284057116301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163242441207051045409488401 122431830905288284057116301)
              ·
                refine ⟨45911936589483106521418613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122431830905288284057116301 45911936589483106521418613)
                ·
                  refine ⟨4304244055264041236382995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45911936589483106521418613 4304244055264041236382995)
                  ·
                    refine ⟨6456366082896061854574493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4304244055264041236382995 6456366082896061854574493)
                    ·
                      refine ⟨2421137281086023195465435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6456366082896061854574493 2421137281086023195465435)
                      ·
                        rfl

theorem cell23_4715148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_4715148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715148 prefixEnd_4715148 := by exact prefixLift 4715148
  have htrace : WordTrace (prefixWord ++ tailWord_4715148) baseStart_4715148 baseEnd_4715148 := by
    simpa [prefixWord, tailWord_4715148, baseEnd_4715148] using wordTrace_append hprefix tailTrace_4715148
  have hstable : (prefixWord ++ tailWord_4715148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715148).length < 2 ^ (prefixWord ++ tailWord_4715148).sum := by decide
  have hdescent : baseEnd_4715148 < baseStart_4715148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715198 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_4715198 : Nat := 118140960795 + 4715198 * 2 ^ 59
def prefixEnd_4715198 : Nat := 4983230072969 + 3 ^ 40 * 4715198 * 2
def baseEnd_4715198 : Nat := 807054318372915999946735

theorem tailTrace_4715198 : CollatzResearch.WordTrace tailWord_4715198 prefixEnd_4715198 807054318372915999946735 := by
  unfold tailWord_4715198
  simp only [CollatzResearch.WordTrace]
  refine ⟨21497174946456301568870281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114651599714433608367308165 21497174946456301568870281)
  ·
    refine ⟨16122881209842226176652711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21497174946456301568870281 16122881209842226176652711)
    ·
      refine ⟨24184321814763339264979067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16122881209842226176652711 24184321814763339264979067)
      ·
        refine ⟨36276482722145008897468601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24184321814763339264979067 36276482722145008897468601)
        ·
          refine ⟨27207362041608756673101451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36276482722145008897468601 27207362041608756673101451)
          ·
            refine ⟨40811043062413135009652177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27207362041608756673101451 40811043062413135009652177)
            ·
              refine ⟨30608282296809851257239133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40811043062413135009652177 30608282296809851257239133)
              ·
                refine ⟨11478105861303694221464675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30608282296809851257239133 11478105861303694221464675)
                ·
                  refine ⟨17217158791955541332197013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11478105861303694221464675 17217158791955541332197013)
                  ·
                    refine ⟨807054318372915999946735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17217158791955541332197013 807054318372915999946735)
                    ·
                      rfl

theorem cell23_4715198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_4715198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715198 prefixEnd_4715198 := by exact prefixLift 4715198
  have htrace : WordTrace (prefixWord ++ tailWord_4715198) baseStart_4715198 baseEnd_4715198 := by
    simpa [prefixWord, tailWord_4715198, baseEnd_4715198] using wordTrace_append hprefix tailTrace_4715198
  have hstable : (prefixWord ++ tailWord_4715198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715198).length < 2 ^ (prefixWord ++ tailWord_4715198).sum := by decide
  have hdescent : baseEnd_4715198 < baseStart_4715198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715228 : List Nat := [2, 2, 5, 1, 1, 12]
def baseStart_4715228 : Nat := 118140960795 + 4715228 * 2 ^ 59
def prefixEnd_4715228 : Nat := 4983230072969 + 3 ^ 40 * 4715228 * 2
def baseEnd_4715228 : Nat := 9963696952832851368169

theorem tailTrace_4715228 : CollatzResearch.WordTrace tailWord_4715228 prefixEnd_4715228 9963696952832851368169 := by
  unfold tailWord_4715228
  simp only [CollatzResearch.WordTrace]
  refine ⟨85989246880770863837277169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114652329174361151783036225 85989246880770863837277169)
  ·
    refine ⟨64491935160578147877957877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85989246880770863837277169 64491935160578147877957877)
    ·
      refine ⟨6046118921304201363558551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64491935160578147877957877 6046118921304201363558551)
      ·
        refine ⟨9069178381956302045337827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046118921304201363558551 9069178381956302045337827)
        ·
          refine ⟨13603767572934453068006741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069178381956302045337827 13603767572934453068006741)
          ·
            refine ⟨9963696952832851368169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13603767572934453068006741 9963696952832851368169)
            ·
              rfl

theorem cell23_4715228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 12].length) (baseStart_4715228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715228 prefixEnd_4715228 := by exact prefixLift 4715228
  have htrace : WordTrace (prefixWord ++ tailWord_4715228) baseStart_4715228 baseEnd_4715228 := by
    simpa [prefixWord, tailWord_4715228, baseEnd_4715228] using wordTrace_append hprefix tailTrace_4715228
  have hstable : (prefixWord ++ tailWord_4715228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715228).length < 2 ^ (prefixWord ++ tailWord_4715228).sum := by decide
  have hdescent : baseEnd_4715228 < baseStart_4715228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715241 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 2, 7]
def baseStart_4715241 : Nat := 118140960795 + 4715241 * 2 ^ 59
def prefixEnd_4715241 : Nat := 4983230072969 + 3 ^ 40 * 4715241 * 2
def baseEnd_4715241 : Nat := 807061678262297110534169

theorem tailTrace_4715241 : CollatzResearch.WordTrace tailWord_4715241 prefixEnd_4715241 807061678262297110534169 := by
  unfold tailWord_4715241
  simp only [CollatzResearch.WordTrace]
  refine ⟨171978967910494630894777577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114652645273663087263185051 171978967910494630894777577)
  ·
    refine ⟨128984225932870973171083183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171978967910494630894777577 128984225932870973171083183)
    ·
      refine ⟨193476338899306459756624775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128984225932870973171083183 193476338899306459756624775)
      ·
        refine ⟨290214508348959689634937163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193476338899306459756624775 290214508348959689634937163)
        ·
          refine ⟨435321762523439534452405745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290214508348959689634937163 435321762523439534452405745)
          ·
            refine ⟨326491321892579650839304309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435321762523439534452405745 326491321892579650839304309)
            ·
              refine ⟨30608561427429342266184779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 326491321892579650839304309 30608561427429342266184779)
              ·
                refine ⟨45912842141144013399277169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30608561427429342266184779 45912842141144013399277169)
                ·
                  refine ⟨34434631605858010049457877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45912842141144013399277169 34434631605858010049457877)
                  ·
                    refine ⟨807061678262297110534169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34434631605858010049457877 807061678262297110534169)
                    ·
                      rfl

theorem cell23_4715241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_4715241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715241 prefixEnd_4715241 := by exact prefixLift 4715241
  have htrace : WordTrace (prefixWord ++ tailWord_4715241) baseStart_4715241 baseEnd_4715241 := by
    simpa [prefixWord, tailWord_4715241, baseEnd_4715241] using wordTrace_append hprefix tailTrace_4715241
  have hstable : (prefixWord ++ tailWord_4715241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715241).length < 2 ^ (prefixWord ++ tailWord_4715241).sum := by decide
  have hdescent : baseEnd_4715241 < baseStart_4715241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715251 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5]
def baseStart_4715251 : Nat := 118140960795 + 4715251 * 2 ^ 59
def prefixEnd_4715251 : Nat := 4983230072969 + 3 ^ 40 * 4715251 * 2
def baseEnd_4715251 : Nat := 2421190169593436292477461

theorem tailTrace_4715251 : CollatzResearch.WordTrace tailWord_4715251 prefixEnd_4715251 2421190169593436292477461 := by
  unfold tailWord_4715251
  simp only [CollatzResearch.WordTrace]
  refine ⟨171979332640458402602641607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114652888426972268401761071 171979332640458402602641607)
  ·
    refine ⟨257968998960687603903962411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171979332640458402602641607 257968998960687603903962411)
    ·
      refine ⟨386953498441031405855943617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257968998960687603903962411 386953498441031405855943617)
      ·
        refine ⟨290215123830773554391957713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386953498441031405855943617 290215123830773554391957713)
        ·
          refine ⟨217661342873080165793968285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290215123830773554391957713 217661342873080165793968285)
          ·
            refine ⟨81623003577405062172738107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217661342873080165793968285 81623003577405062172738107)
            ·
              refine ⟨122434505366107593259107161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81623003577405062172738107 122434505366107593259107161)
              ·
                refine ⟨91825879024580694944330371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122434505366107593259107161 91825879024580694944330371)
                ·
                  refine ⟨137738818536871042416495557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91825879024580694944330371 137738818536871042416495557)
                  ·
                    refine ⟨25826028475663320453092917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137738818536871042416495557 25826028475663320453092917)
                    ·
                      refine ⟨2421190169593436292477461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25826028475663320453092917 2421190169593436292477461)
                      ·
                        rfl

theorem cell23_4715251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_4715251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715251 prefixEnd_4715251 := by exact prefixLift 4715251
  have htrace : WordTrace (prefixWord ++ tailWord_4715251) baseStart_4715251 baseEnd_4715251 := by
    simpa [prefixWord, tailWord_4715251, baseEnd_4715251] using wordTrace_append hprefix tailTrace_4715251
  have hstable : (prefixWord ++ tailWord_4715251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715251).length < 2 ^ (prefixWord ++ tailWord_4715251).sum := by decide
  have hdescent : baseEnd_4715251 < baseStart_4715251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715268 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4715268 : Nat := 118140960795 + 4715268 * 2 ^ 59
def prefixEnd_4715268 : Nat := 4983230072969 + 3 ^ 40 * 4715268 * 2
def baseEnd_4715268 : Nat := 2421198898764562725964883

theorem tailTrace_4715268 : CollatzResearch.WordTrace tailWord_4715268 prefixEnd_4715268 2421198898764562725964883 := by
  unfold tailWord_4715268
  simp only [CollatzResearch.WordTrace]
  refine ⟨85989976340698407253005229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114653301787597876337340305 85989976340698407253005229)
  ·
    refine ⟨32246241127761902719876961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85989976340698407253005229 32246241127761902719876961)
    ·
      refine ⟨24184680845821427039907721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32246241127761902719876961 24184680845821427039907721)
      ·
        refine ⟨18138510634366070279930791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24184680845821427039907721 18138510634366070279930791)
        ·
          refine ⟨27207765951549105419896187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18138510634366070279930791 27207765951549105419896187)
          ·
            refine ⟨40811648927323658129844281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27207765951549105419896187 40811648927323658129844281)
            ·
              refine ⟨30608736695492743597383211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40811648927323658129844281 30608736695492743597383211)
              ·
                refine ⟨45913105043239115396074817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30608736695492743597383211 45913105043239115396074817)
                ·
                  refine ⟨34434828782429336547056113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45913105043239115396074817 34434828782429336547056113)
                  ·
                    refine ⟨25826121586822002410292085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34434828782429336547056113 25826121586822002410292085)
                    ·
                      refine ⟨2421198898764562725964883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25826121586822002410292085 2421198898764562725964883)
                      ·
                        rfl

theorem cell23_4715268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4715268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715268 prefixEnd_4715268 := by exact prefixLift 4715268
  have htrace : WordTrace (prefixWord ++ tailWord_4715268) baseStart_4715268 baseEnd_4715268 := by
    simpa [prefixWord, tailWord_4715268, baseEnd_4715268] using wordTrace_append hprefix tailTrace_4715268
  have hstable : (prefixWord ++ tailWord_4715268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715268).length < 2 ^ (prefixWord ++ tailWord_4715268).sum := by decide
  have hdescent : baseEnd_4715268 < baseStart_4715268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715291 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6]
def baseStart_4715291 : Nat := 118140960795 + 4715291 * 2 ^ 59
def prefixEnd_4715291 : Nat := 4983230072969 + 3 ^ 40 * 4715291 * 2
def baseEnd_4715291 : Nat := 2421210708819616135977277

theorem tailTrace_4715291 : CollatzResearch.WordTrace tailWord_4715291 prefixEnd_4715291 2421210708819616135977277 := by
  unfold tailWord_4715291
  simp only [CollatzResearch.WordTrace]
  refine ⟨171980791560313489434097727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114653861040208992956065151 171980791560313489434097727)
  ·
    refine ⟨257971187340470234151146591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171980791560313489434097727 257971187340470234151146591)
    ·
      refine ⟨386956781010705351226719887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257971187340470234151146591 386956781010705351226719887)
      ·
        refine ⟨580435171516058026840079831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386956781010705351226719887 580435171516058026840079831)
        ·
          refine ⟨870652757274087040260119747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580435171516058026840079831 870652757274087040260119747)
          ·
            refine ⟨1305979135911130560390179621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870652757274087040260119747 1305979135911130560390179621)
            ·
              refine ⟨244871087983336980073158679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1305979135911130560390179621 244871087983336980073158679)
              ·
                refine ⟨367306631975005470109738019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244871087983336980073158679 367306631975005470109738019)
                ·
                  refine ⟨550959947962508205164607029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367306631975005470109738019 550959947962508205164607029)
                  ·
                    refine ⟨51652495121485144234181909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 550959947962508205164607029 51652495121485144234181909)
                    ·
                      refine ⟨2421210708819616135977277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51652495121485144234181909 2421210708819616135977277)
                      ·
                        rfl

theorem cell23_4715291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_4715291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715291 prefixEnd_4715291 := by exact prefixLift 4715291
  have htrace : WordTrace (prefixWord ++ tailWord_4715291) baseStart_4715291 baseEnd_4715291 := by
    simpa [prefixWord, tailWord_4715291, baseEnd_4715291] using wordTrace_append hprefix tailTrace_4715291
  have hstable : (prefixWord ++ tailWord_4715291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715291).length < 2 ^ (prefixWord ++ tailWord_4715291).sum := by decide
  have hdescent : baseEnd_4715291 < baseStart_4715291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715306 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4715306 : Nat := 118140960795 + 4715306 * 2 ^ 59
def prefixEnd_4715306 : Nat := 4983230072969 + 3 ^ 40 * 4715306 * 2
def baseEnd_4715306 : Nat := 2421218411029433577289709

theorem tailTrace_4715306 : CollatzResearch.WordTrace tailWord_4715306 prefixEnd_4715306 2421218411029433577289709 := by
  unfold tailWord_4715306
  simp only [CollatzResearch.WordTrace]
  refine ⟨42995334663814786748973443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114654225770172764663929181 42995334663814786748973443)
  ·
    refine ⟨64493001995722180123460165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42995334663814786748973443 64493001995722180123460165)
    ·
      refine ⟨12092437874197908773148781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64493001995722180123460165 12092437874197908773148781)
      ·
        refine ⟨4534664202824215789930793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12092437874197908773148781 4534664202824215789930793)
        ·
          refine ⟨3400998152118161842448095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4534664202824215789930793 3400998152118161842448095)
          ·
            refine ⟨5101497228177242763672143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400998152118161842448095 5101497228177242763672143)
            ·
              refine ⟨7652245842265864145508215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101497228177242763672143 7652245842265864145508215)
              ·
                refine ⟨11478368763398796218262323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7652245842265864145508215 11478368763398796218262323)
                ·
                  refine ⟨17217553145098194327393485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11478368763398796218262323 17217553145098194327393485)
                  ·
                    refine ⟨6456582429411822872772557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17217553145098194327393485 6456582429411822872772557)
                    ·
                      refine ⟨2421218411029433577289709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6456582429411822872772557 2421218411029433577289709)
                      ·
                        rfl

theorem cell23_4715306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4715306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715306 prefixEnd_4715306 := by exact prefixLift 4715306
  have htrace : WordTrace (prefixWord ++ tailWord_4715306) baseStart_4715306 baseEnd_4715306 := by
    simpa [prefixWord, tailWord_4715306, baseEnd_4715306] using wordTrace_append hprefix tailTrace_4715306
  have hstable : (prefixWord ++ tailWord_4715306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715306).length < 2 ^ (prefixWord ++ tailWord_4715306).sum := by decide
  have hdescent : baseEnd_4715306 < baseStart_4715306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715308 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_4715308 : Nat := 118140960795 + 4715308 * 2 ^ 59
def prefixEnd_4715308 : Nat := 4983230072969 + 3 ^ 40 * 4715308 * 2
def baseEnd_4715308 : Nat := 2421219437990742569464699

theorem tailTrace_4715308 : CollatzResearch.WordTrace tailWord_4715308 prefixEnd_4715308 2421219437990742569464699 := by
  unfold tailWord_4715308
  simp only [CollatzResearch.WordTrace]
  refine ⟨85990705800625950668733289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114654274400834600891644385 85990705800625950668733289)
  ·
    refine ⟨64493029350469463001549967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85990705800625950668733289 64493029350469463001549967)
    ·
      refine ⟨96739544025704194502324951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64493029350469463001549967 96739544025704194502324951)
      ·
        refine ⟨145109316038556291753487427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96739544025704194502324951 145109316038556291753487427)
        ·
          refine ⟨217663974057834437630231141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145109316038556291753487427 217663974057834437630231141)
          ·
            refine ⟨40811995135843957055668339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217663974057834437630231141 40811995135843957055668339)
            ·
              refine ⟨61217992703765935583502509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40811995135843957055668339 61217992703765935583502509)
              ·
                refine ⟨22956747263912225843813441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61217992703765935583502509 22956747263912225843813441)
                ·
                  refine ⟨17217560447934169382860081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22956747263912225843813441 17217560447934169382860081)
                  ·
                    refine ⟨12913170335950627037145061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17217560447934169382860081 12913170335950627037145061)
                    ·
                      refine ⟨2421219437990742569464699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12913170335950627037145061 2421219437990742569464699)
                      ·
                        rfl

theorem cell23_4715308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_4715308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715308 prefixEnd_4715308 := by exact prefixLift 4715308
  have htrace : WordTrace (prefixWord ++ tailWord_4715308) baseStart_4715308 baseEnd_4715308 := by
    simpa [prefixWord, tailWord_4715308, baseEnd_4715308] using wordTrace_append hprefix tailTrace_4715308
  have hstable : (prefixWord ++ tailWord_4715308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715308).length < 2 ^ (prefixWord ++ tailWord_4715308).sum := by decide
  have hdescent : baseEnd_4715308 < baseStart_4715308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715312 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 2, 2, 2]
def baseStart_4715312 : Nat := 118140960795 + 4715312 * 2 ^ 59
def prefixEnd_4715312 : Nat := 4983230072969 + 3 ^ 40 * 4715312 * 2
def baseEnd_4715312 : Nat := 2421221491913360553814681

theorem tailTrace_4715312 : CollatzResearch.WordTrace tailWord_4715312 prefixEnd_4715312 2421221491913360553814681 := by
  unfold tailWord_4715312
  simp only [CollatzResearch.WordTrace]
  refine ⟨85990778746618705010306095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114654371662158273347074793 85990778746618705010306095)
  ·
    refine ⟨128986168119928057515459143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85990778746618705010306095 128986168119928057515459143)
    ·
      refine ⟨193479252179892086273188715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128986168119928057515459143 193479252179892086273188715)
      ·
        refine ⟨290218878269838129409783073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193479252179892086273188715 290218878269838129409783073)
        ·
          refine ⟨217664158702378597057337305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290218878269838129409783073 217664158702378597057337305)
          ·
            refine ⟨163248119026783947793002979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217664158702378597057337305 163248119026783947793002979)
            ·
              refine ⟨244872178540175921689504469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163248119026783947793002979 244872178540175921689504469)
              ·
                refine ⟨5739191684535373164597761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 244872178540175921689504469 5739191684535373164597761)
                ·
                  refine ⟨4304393763401529873448321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5739191684535373164597761 4304393763401529873448321)
                  ·
                    refine ⟨3228295322551147405086241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4304393763401529873448321 3228295322551147405086241)
                    ·
                      refine ⟨2421221491913360553814681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228295322551147405086241 2421221491913360553814681)
                      ·
                        rfl

theorem cell23_4715312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 2, 2].length) (baseStart_4715312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715312 prefixEnd_4715312 := by exact prefixLift 4715312
  have htrace : WordTrace (prefixWord ++ tailWord_4715312) baseStart_4715312 baseEnd_4715312 := by
    simpa [prefixWord, tailWord_4715312, baseEnd_4715312] using wordTrace_append hprefix tailTrace_4715312
  have hstable : (prefixWord ++ tailWord_4715312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715312).length < 2 ^ (prefixWord ++ tailWord_4715312).sum := by decide
  have hdescent : baseEnd_4715312 < baseStart_4715312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715316 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_4715316 : Nat := 118140960795 + 4715316 * 2 ^ 59
def prefixEnd_4715316 : Nat := 4983230072969 + 3 ^ 40 * 4715316 * 2
def baseEnd_4715316 : Nat := 2421223545835978538164663

theorem tailTrace_4715316 : CollatzResearch.WordTrace tailWord_4715316 prefixEnd_4715316 2421223545835978538164663 := by
  unfold tailWord_4715316
  simp only [CollatzResearch.WordTrace]
  refine ⟨85990851692611459351878901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114654468923481945802505201 85990851692611459351878901)
  ·
    refine ⟨8061642346182324314238647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85990851692611459351878901 8061642346182324314238647)
    ·
      refine ⟨12092463519273486471357971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8061642346182324314238647 12092463519273486471357971)
      ·
        refine ⟨18138695278910229707036957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12092463519273486471357971 18138695278910229707036957)
        ·
          refine ⟨6802010729591336140138859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18138695278910229707036957 6802010729591336140138859)
          ·
            refine ⟨10203016094387004210208289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6802010729591336140138859 10203016094387004210208289)
            ·
              refine ⟨7652262070790253157656217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10203016094387004210208289 7652262070790253157656217)
              ·
                refine ⟨5739196553092689868242163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7652262070790253157656217 5739196553092689868242163)
                ·
                  refine ⟨8608794829639034802363245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5739196553092689868242163 8608794829639034802363245)
                  ·
                    refine ⟨3228298061114638050886217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8608794829639034802363245 3228298061114638050886217)
                    ·
                      refine ⟨2421223545835978538164663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228298061114638050886217 2421223545835978538164663)
                      ·
                        rfl

theorem cell23_4715316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_4715316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715316 prefixEnd_4715316 := by exact prefixLift 4715316
  have htrace : WordTrace (prefixWord ++ tailWord_4715316) baseStart_4715316 baseEnd_4715316 := by
    simpa [prefixWord, tailWord_4715316, baseEnd_4715316] using wordTrace_append hprefix tailTrace_4715316
  have hstable : (prefixWord ++ tailWord_4715316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715316).length < 2 ^ (prefixWord ++ tailWord_4715316).sum := by decide
  have hdescent : baseEnd_4715316 < baseStart_4715316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715328 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3]
def baseStart_4715328 : Nat := 118140960795 + 4715328 * 2 ^ 59
def prefixEnd_4715328 : Nat := 4983230072969 + 3 ^ 40 * 4715328 * 2
def baseEnd_4715328 : Nat := 2421229707603832491214607

theorem tailTrace_4715328 : CollatzResearch.WordTrace tailWord_4715328 prefixEnd_4715328 2421229707603832491214607 := by
  unfold tailWord_4715328
  simp only [CollatzResearch.WordTrace]
  refine ⟨85991070530589722376597319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114654760707452963168796425 85991070530589722376597319)
  ·
    refine ⟨128986605795884583564895979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85991070530589722376597319 128986605795884583564895979)
    ·
      refine ⟨193479908693826875347343969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128986605795884583564895979 193479908693826875347343969)
      ·
        refine ⟨145109931520370156510507977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193479908693826875347343969 145109931520370156510507977)
        ·
          refine ⟨108832448640277617382880983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145109931520370156510507977 108832448640277617382880983)
          ·
            refine ⟨163248672960416426074321475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108832448640277617382880983 163248672960416426074321475)
            ·
              refine ⟨244873009440624639111482213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163248672960416426074321475 244873009440624639111482213)
              ·
                refine ⟨45913689270117119833402915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244873009440624639111482213 45913689270117119833402915)
                ·
                  refine ⟨68870533905175679750104373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45913689270117119833402915 68870533905175679750104373)
                  ·
                    refine ⟨6456612553610219976572285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68870533905175679750104373 6456612553610219976572285)
                    ·
                      refine ⟨2421229707603832491214607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6456612553610219976572285 2421229707603832491214607)
                      ·
                        rfl

theorem cell23_4715328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_4715328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715328 prefixEnd_4715328 := by exact prefixLift 4715328
  have htrace : WordTrace (prefixWord ++ tailWord_4715328) baseStart_4715328 baseEnd_4715328 := by
    simpa [prefixWord, tailWord_4715328, baseEnd_4715328] using wordTrace_append hprefix tailTrace_4715328
  have hstable : (prefixWord ++ tailWord_4715328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715328).length < 2 ^ (prefixWord ++ tailWord_4715328).sum := by decide
  have hdescent : baseEnd_4715328 < baseStart_4715328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715378 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_4715378 : Nat := 118140960795 + 4715378 * 2 ^ 59
def prefixEnd_4715378 : Nat := 4983230072969 + 3 ^ 40 * 4715378 * 2
def baseEnd_4715378 : Nat := 807085127212185765196459

theorem tailTrace_4715378 : CollatzResearch.WordTrace tailWord_4715378 prefixEnd_4715378 807085127212185765196459 := by
  unfold tailWord_4715378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42995991177749575823128697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114655976473998868861676525 42995991177749575823128697)
  ·
    refine ⟨32246993383312181867346523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42995991177749575823128697 32246993383312181867346523)
    ·
      refine ⟨48370490074968272801019785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32246993383312181867346523 48370490074968272801019785)
      ·
        refine ⟨36277867556226204600764839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48370490074968272801019785 36277867556226204600764839)
        ·
          refine ⟨54416801334339306901147259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36277867556226204600764839 54416801334339306901147259)
          ·
            refine ⟨81625202001508960351720889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54416801334339306901147259 81625202001508960351720889)
            ·
              refine ⟨61218901501131720263790667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81625202001508960351720889 61218901501131720263790667)
              ·
                refine ⟨91828352251697580395686001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61218901501131720263790667 91828352251697580395686001)
                ·
                  refine ⟨68871264188773185296764501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91828352251697580395686001 68871264188773185296764501)
                  ·
                    refine ⟨807085127212185765196459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68871264188773185296764501 807085127212185765196459)
                    ·
                      rfl

theorem cell23_4715378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_4715378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715378 prefixEnd_4715378 := by exact prefixLift 4715378
  have htrace : WordTrace (prefixWord ++ tailWord_4715378) baseStart_4715378 baseEnd_4715378 := by
    simpa [prefixWord, tailWord_4715378, baseEnd_4715378] using wordTrace_append hprefix tailTrace_4715378
  have hstable : (prefixWord ++ tailWord_4715378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715378).length < 2 ^ (prefixWord ++ tailWord_4715378).sum := by decide
  have hdescent : baseEnd_4715378 < baseStart_4715378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715382 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_4715382 : Nat := 118140960795 + 4715382 * 2 ^ 59
def prefixEnd_4715382 : Nat := 4983230072969 + 3 ^ 40 * 4715382 * 2
def baseEnd_4715382 : Nat := 807085811853058426646453

theorem tailTrace_4715382 : CollatzResearch.WordTrace tailWord_4715382 prefixEnd_4715382 807085811853058426646453 := by
  unfold tailWord_4715382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10749006912686488248478775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114656073735322541317106933 10749006912686488248478775)
  ·
    refine ⟨16123510369029732372718163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10749006912686488248478775 16123510369029732372718163)
    ·
      refine ⟨24185265553544598559077245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16123510369029732372718163 24185265553544598559077245)
      ·
        refine ⟨9069474582579224459653967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24185265553544598559077245 9069474582579224459653967)
        ·
          refine ⟨13604211873868836689480951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069474582579224459653967 13604211873868836689480951)
          ·
            refine ⟨20406317810803255034221427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13604211873868836689480951 20406317810803255034221427)
            ·
              refine ⟨30609476716204882551332141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20406317810803255034221427 30609476716204882551332141)
              ·
                refine ⟨11478553768576830956749553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30609476716204882551332141 11478553768576830956749553)
                ·
                  refine ⟨8608915326432623217562165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11478553768576830956749553 8608915326432623217562165)
                  ·
                    refine ⟨807085811853058426646453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8608915326432623217562165 807085811853058426646453)
                    ·
                      rfl

theorem cell23_4715382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_4715382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715382 prefixEnd_4715382 := by exact prefixLift 4715382
  have htrace : WordTrace (prefixWord ++ tailWord_4715382) baseStart_4715382 baseEnd_4715382 := by
    simpa [prefixWord, tailWord_4715382, baseEnd_4715382] using wordTrace_append hprefix tailTrace_4715382
  have hstable : (prefixWord ++ tailWord_4715382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715382).length < 2 ^ (prefixWord ++ tailWord_4715382).sum := by decide
  have hdescent : baseEnd_4715382 < baseStart_4715382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715385 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_4715385 : Nat := 118140960795 + 4715385 * 2 ^ 59
def prefixEnd_4715385 : Nat := 4983230072969 + 3 ^ 40 * 4715385 * 2
def baseEnd_4715385 : Nat := 2421258976001138768201845

theorem tailTrace_4715385 : CollatzResearch.WordTrace tailWord_4715385 prefixEnd_4715385 2421258976001138768201845 := by
  unfold tailWord_4715385
  simp only [CollatzResearch.WordTrace]
  refine ⟨171984220021972943488019609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114656146681315295658679739 171984220021972943488019609)
  ·
    refine ⟨128988165016479707616014707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171984220021972943488019609 128988165016479707616014707)
    ·
      refine ⟨193482247524719561424022061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128988165016479707616014707 193482247524719561424022061)
      ·
        refine ⟨72555842821769835534008273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193482247524719561424022061 72555842821769835534008273)
        ·
          refine ⟨54416882116327376650506205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72555842821769835534008273 54416882116327376650506205)
          ·
            refine ⟨20406330793622766243939827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54416882116327376650506205 20406330793622766243939827)
            ·
              refine ⟨30609496190434149365909741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20406330793622766243939827 30609496190434149365909741)
              ·
                refine ⟨11478561071412806012216153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30609496190434149365909741 11478561071412806012216153)
                ·
                  refine ⟨8608920803559604509162115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11478561071412806012216153 8608920803559604509162115)
                  ·
                    refine ⟨12913381205339406763743173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8608920803559604509162115 12913381205339406763743173)
                    ·
                      refine ⟨2421258976001138768201845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12913381205339406763743173 2421258976001138768201845)
                      ·
                        rfl

theorem cell23_4715385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_4715385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715385 prefixEnd_4715385 := by exact prefixLift 4715385
  have htrace : WordTrace (prefixWord ++ tailWord_4715385) baseStart_4715385 baseEnd_4715385 := by
    simpa [prefixWord, tailWord_4715385, baseEnd_4715385] using wordTrace_append hprefix tailTrace_4715385
  have hstable : (prefixWord ++ tailWord_4715385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715385).length < 2 ^ (prefixWord ++ tailWord_4715385).sum := by decide
  have hdescent : baseEnd_4715385 < baseStart_4715385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715402 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4715402 : Nat := 118140960795 + 4715402 * 2 ^ 59
def prefixEnd_4715402 : Nat := 4983230072969 + 3 ^ 40 * 4715402 * 2
def baseEnd_4715402 : Nat := 2421267705172265201689267

theorem tailTrace_4715402 : CollatzResearch.WordTrace tailWord_4715402 prefixEnd_4715402 2421267705172265201689267 := by
  unfold tailWord_4715402
  simp only [CollatzResearch.WordTrace]
  refine ⟨42996210015727838847847115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114656560041940903594258973 42996210015727838847847115)
  ·
    refine ⟨64494315023591758271770673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42996210015727838847847115 64494315023591758271770673)
    ·
      refine ⟨48370736267693818703828005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64494315023591758271770673 48370736267693818703828005)
      ·
        refine ⟨9069513050192591006967751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48370736267693818703828005 9069513050192591006967751)
        ·
          refine ⟨13604269575288886510451627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069513050192591006967751 13604269575288886510451627)
          ·
            refine ⟨20406404362933329765677441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13604269575288886510451627 20406404362933329765677441)
            ·
              refine ⟨15304803272199997324258081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20406404362933329765677441 15304803272199997324258081)
              ·
                refine ⟨11478602454149997993193561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15304803272199997324258081 11478602454149997993193561)
                ·
                  refine ⟨8608951840612498494895171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11478602454149997993193561 8608951840612498494895171)
                  ·
                    refine ⟨12913427760918747742342757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8608951840612498494895171 12913427760918747742342757)
                    ·
                      refine ⟨2421267705172265201689267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12913427760918747742342757 2421267705172265201689267)
                      ·
                        rfl

theorem cell23_4715402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4715402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715402 prefixEnd_4715402 := by exact prefixLift 4715402
  have htrace : WordTrace (prefixWord ++ tailWord_4715402) baseStart_4715402 baseEnd_4715402 := by
    simpa [prefixWord, tailWord_4715402, baseEnd_4715402] using wordTrace_append hprefix tailTrace_4715402
  have hstable : (prefixWord ++ tailWord_4715402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715402).length < 2 ^ (prefixWord ++ tailWord_4715402).sum := by decide
  have hdescent : baseEnd_4715402 < baseStart_4715402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715412 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4715412 : Nat := 118140960795 + 4715412 * 2 ^ 59
def prefixEnd_4715412 : Nat := 4983230072969 + 3 ^ 40 * 4715412 * 2
def baseEnd_4715412 : Nat := 807090946659603387521407

theorem tailTrace_4715412 : CollatzResearch.WordTrace tailWord_4715412 prefixEnd_4715412 807090946659603387521407 := by
  unfold tailWord_4715412
  simp only [CollatzResearch.WordTrace]
  refine ⟨85992602396437563549626245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114656803195250084732834993 85992602396437563549626245)
  ·
    refine ⟨16123612949332043165554921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85992602396437563549626245 16123612949332043165554921)
    ·
      refine ⟨12092709711999032374166191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16123612949332043165554921 12092709711999032374166191)
      ·
        refine ⟨18139064567998548561249287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12092709711999032374166191 18139064567998548561249287)
        ·
          refine ⟨27208596851997822841873931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18139064567998548561249287 27208596851997822841873931)
          ·
            refine ⟨40812895277996734262810897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27208596851997822841873931 40812895277996734262810897)
            ·
              refine ⟨30609671458497550697108173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40812895277996734262810897 30609671458497550697108173)
              ·
                refine ⟨11478626796936581511415565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30609671458497550697108173 11478626796936581511415565)
                ·
                  refine ⟨4304485048851218066780837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11478626796936581511415565 4304485048851218066780837)
                  ·
                    refine ⟨807090946659603387521407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304485048851218066780837 807090946659603387521407)
                    ·
                      rfl

theorem cell23_4715412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4715412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715412 prefixEnd_4715412 := by exact prefixLift 4715412
  have htrace : WordTrace (prefixWord ++ tailWord_4715412) baseStart_4715412 baseEnd_4715412 := by
    simpa [prefixWord, tailWord_4715412, baseEnd_4715412] using wordTrace_append hprefix tailTrace_4715412
  have hstable : (prefixWord ++ tailWord_4715412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715412).length < 2 ^ (prefixWord ++ tailWord_4715412).sum := by decide
  have hdescent : baseEnd_4715412 < baseStart_4715412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715559 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4715559 : Nat := 118140960795 + 4715559 * 2 ^ 59
def prefixEnd_4715559 : Nat := 4983230072969 + 3 ^ 40 * 4715559 * 2
def baseEnd_4715559 : Nat := 2421348321635021087426045

theorem tailTrace_4715559 : CollatzResearch.WordTrace tailWord_4715559 prefixEnd_4715559 2421348321635021087426045 := by
  unfold tailWord_4715559
  simp only [CollatzResearch.WordTrace]
  refine ⟨171990566323342571204853731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114660377548895047469902487 171990566323342571204853731)
  ·
    refine ⟨257985849485013856807280597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171990566323342571204853731 257985849485013856807280597)
    ·
      refine ⟨6046543347305012268920639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 257985849485013856807280597 6046543347305012268920639)
      ·
        refine ⟨9069815020957518403380959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046543347305012268920639 9069815020957518403380959)
        ·
          refine ⟨13604722531436277605071439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069815020957518403380959 13604722531436277605071439)
          ·
            refine ⟨20407083797154416407607159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13604722531436277605071439 20407083797154416407607159)
            ·
              refine ⟨30610625695731624611410739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20407083797154416407607159 30610625695731624611410739)
              ·
                refine ⟨45915938543597436917116109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30610625695731624611410739 45915938543597436917116109)
                ·
                  refine ⟨17218476953849038843918541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45915938543597436917116109 17218476953849038843918541)
                  ·
                    refine ⟨6456928857693389566469453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17218476953849038843918541 6456928857693389566469453)
                    ·
                      refine ⟨2421348321635021087426045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6456928857693389566469453 2421348321635021087426045)
                      ·
                        rfl

theorem cell23_4715559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4715559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715559 prefixEnd_4715559 := by exact prefixLift 4715559
  have htrace : WordTrace (prefixWord ++ tailWord_4715559) baseStart_4715559 baseEnd_4715559 := by
    simpa [prefixWord, tailWord_4715559, baseEnd_4715559] using wordTrace_append hprefix tailTrace_4715559
  have hstable : (prefixWord ++ tailWord_4715559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715559).length < 2 ^ (prefixWord ++ tailWord_4715559).sum := by decide
  have hdescent : baseEnd_4715559 < baseStart_4715559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715575 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 2, 6]
def baseStart_4715575 : Nat := 118140960795 + 4715575 * 2 ^ 59
def prefixEnd_4715575 : Nat := 4983230072969 + 3 ^ 40 * 4715575 * 2
def baseEnd_4715575 : Nat := 807118845775164341608657

theorem tailTrace_4715575 : CollatzResearch.WordTrace tailWord_4715575 prefixEnd_4715575 807118845775164341608657 := by
  unfold tailWord_4715575
  simp only [CollatzResearch.WordTrace]
  refine ⟨171991149891284605937436179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114660766594189737291624119 171991149891284605937436179)
  ·
    refine ⟨257986724836926908906154269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171991149891284605937436179 257986724836926908906154269)
    ·
      refine ⟨96745021813847590839807851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257986724836926908906154269 96745021813847590839807851)
      ·
        refine ⟨145117532720771386259711777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96745021813847590839807851 145117532720771386259711777)
        ·
          refine ⟨108838149540578539694783833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145117532720771386259711777 108838149540578539694783833)
          ·
            refine ⟨81628612155433904771087875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108838149540578539694783833 81628612155433904771087875)
            ·
              refine ⟨122442918233150857156631813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81628612155433904771087875 122442918233150857156631813)
              ·
                refine ⟨22958047168715785716868465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122442918233150857156631813 22958047168715785716868465)
                ·
                  refine ⟨17218535376536839287651349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22958047168715785716868465 17218535376536839287651349)
                  ·
                    refine ⟨807118845775164341608657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17218535376536839287651349 807118845775164341608657)
                    ·
                      rfl

theorem cell23_4715575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_4715575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715575 prefixEnd_4715575 := by exact prefixLift 4715575
  have htrace : WordTrace (prefixWord ++ tailWord_4715575) baseStart_4715575 baseEnd_4715575 := by
    simpa [prefixWord, tailWord_4715575, baseEnd_4715575] using wordTrace_append hprefix tailTrace_4715575
  have hstable : (prefixWord ++ tailWord_4715575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715575).length < 2 ^ (prefixWord ++ tailWord_4715575).sum := by decide
  have hdescent : baseEnd_4715575 < baseStart_4715575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715576 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_4715576 : Nat := 118140960795 + 4715576 * 2 ^ 59
def prefixEnd_4715576 : Nat := 4983230072969 + 3 ^ 40 * 4715576 * 2
def baseEnd_4715576 : Nat := 2421357050806147520913467

theorem tailTrace_4715576 : CollatzResearch.WordTrace tailWord_4715576 prefixEnd_4715576 2421357050806147520913467 := by
  unfold tailWord_4715576
  simp only [CollatzResearch.WordTrace]
  refine ⟨85995593182140491554111291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114660790909520655405481721 85995593182140491554111291)
  ·
    refine ⟨128993389773210737331166937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85995593182140491554111291 128993389773210737331166937)
    ·
      refine ⟨96745042329908052998375203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128993389773210737331166937 96745042329908052998375203)
      ·
        refine ⟨145117563494862079497562805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96745042329908052998375203 145117563494862079497562805)
        ·
          refine ⟨13604771577643319952896513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145117563494862079497562805 13604771577643319952896513)
          ·
            refine ⟨10203578683232489964672385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13604771577643319952896513 10203578683232489964672385)
            ·
              refine ⟨7652684012424367473504289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10203578683232489964672385 7652684012424367473504289)
              ·
                refine ⟨5739513009318275605128217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7652684012424367473504289 5739513009318275605128217)
                ·
                  refine ⟨4304634756988706703846163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5739513009318275605128217 4304634756988706703846163)
                  ·
                    refine ⟨6456952135483060055769245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4304634756988706703846163 6456952135483060055769245)
                    ·
                      refine ⟨2421357050806147520913467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6456952135483060055769245 2421357050806147520913467)
                      ·
                        rfl

theorem cell23_4715576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_4715576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715576 prefixEnd_4715576 := by exact prefixLift 4715576
  have htrace : WordTrace (prefixWord ++ tailWord_4715576) baseStart_4715576 baseEnd_4715576 := by
    simpa [prefixWord, tailWord_4715576, baseEnd_4715576] using wordTrace_append hprefix tailTrace_4715576
  have hstable : (prefixWord ++ tailWord_4715576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715576).length < 2 ^ (prefixWord ++ tailWord_4715576).sum := by decide
  have hdescent : baseEnd_4715576 < baseStart_4715576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715612 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4715612 : Nat := 118140960795 + 4715612 * 2 ^ 59
def prefixEnd_4715612 : Nat := 4983230072969 + 3 ^ 40 * 4715612 * 2
def baseEnd_4715612 : Nat := 2421375536109709380063301

theorem tailTrace_4715612 : CollatzResearch.WordTrace tailWord_4715612 prefixEnd_4715612 2421375536109709380063301 := by
  unfold tailWord_4715612
  simp only [CollatzResearch.WordTrace]
  refine ⟨85996249696075280628266545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114661666261433707504355393 85996249696075280628266545)
  ·
    refine ⟨64497187272056460471199909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85996249696075280628266545 64497187272056460471199909)
    ·
      refine ⟨12093222613510586338349983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64497187272056460471199909 12093222613510586338349983)
      ·
        refine ⟨18139833920265879507524975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12093222613510586338349983 18139833920265879507524975)
        ·
          refine ⟨27209750880398819261287463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18139833920265879507524975 27209750880398819261287463)
          ·
            refine ⟨40814626320598228891931195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27209750880398819261287463 40814626320598228891931195)
            ·
              refine ⟨61221939480897343337896793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40814626320598228891931195 61221939480897343337896793)
              ·
                refine ⟨45916454610673007503422595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61221939480897343337896793 45916454610673007503422595)
                ·
                  refine ⟨68874681916009511255133893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45916454610673007503422595 68874681916009511255133893)
                  ·
                    refine ⟨12914002859251783360337605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68874681916009511255133893 12914002859251783360337605)
                    ·
                      refine ⟨2421375536109709380063301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12914002859251783360337605 2421375536109709380063301)
                      ·
                        rfl

theorem cell23_4715612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4715612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715612 prefixEnd_4715612 := by exact prefixLift 4715612
  have htrace : WordTrace (prefixWord ++ tailWord_4715612) baseStart_4715612 baseEnd_4715612 := by
    simpa [prefixWord, tailWord_4715612, baseEnd_4715612] using wordTrace_append hprefix tailTrace_4715612
  have hstable : (prefixWord ++ tailWord_4715612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715612).length < 2 ^ (prefixWord ++ tailWord_4715612).sum := by decide
  have hdescent : baseEnd_4715612 < baseStart_4715612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715632 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3]
def baseStart_4715632 : Nat := 118140960795 + 4715632 * 2 ^ 59
def prefixEnd_4715632 : Nat := 4983230072969 + 3 ^ 40 * 4715632 * 2
def baseEnd_4715632 : Nat := 2421385805722799301813209

theorem tailTrace_4715632 : CollatzResearch.WordTrace tailWord_4715632 prefixEnd_4715632 2421385805722799301813209 := by
  unfold tailWord_4715632
  simp only [CollatzResearch.WordTrace]
  refine ⟨85996614426039052336130575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114662152568052069781507433 85996614426039052336130575)
  ·
    refine ⟨128994921639058578504195863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85996614426039052336130575 128994921639058578504195863)
    ·
      refine ⟨193492382458587867756293795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128994921639058578504195863 193492382458587867756293795)
      ·
        refine ⟨290238573687881801634440693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193492382458587867756293795 290238573687881801634440693)
        ·
          refine ⟨27209866283238918903228815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 290238573687881801634440693 27209866283238918903228815)
          ·
            refine ⟨40814799424858378354843223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27209866283238918903228815 40814799424858378354843223)
            ·
              refine ⟨61222199137287567532264835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40814799424858378354843223 61222199137287567532264835)
              ·
                refine ⟨91833298705931351298397253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61222199137287567532264835 91833298705931351298397253)
                ·
                  refine ⟨17218743507362128368449485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91833298705931351298397253 17218743507362128368449485)
                  ·
                    refine ⟨6457028815260798138168557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17218743507362128368449485 6457028815260798138168557)
                    ·
                      refine ⟨2421385805722799301813209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6457028815260798138168557 2421385805722799301813209)
                      ·
                        rfl

theorem cell23_4715632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_4715632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715632 prefixEnd_4715632 := by exact prefixLift 4715632
  have htrace : WordTrace (prefixWord ++ tailWord_4715632) baseStart_4715632 baseEnd_4715632 := by
    simpa [prefixWord, tailWord_4715632, baseEnd_4715632] using wordTrace_append hprefix tailTrace_4715632
  have hstable : (prefixWord ++ tailWord_4715632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715632).length < 2 ^ (prefixWord ++ tailWord_4715632).sum := by decide
  have hdescent : baseEnd_4715632 < baseStart_4715632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715649 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_4715649 : Nat := 118140960795 + 4715649 * 2 ^ 59
def prefixEnd_4715649 : Nat := 4983230072969 + 3 ^ 40 * 4715649 * 2
def baseEnd_4715649 : Nat := 2421394534893925735300631

theorem tailTrace_4715649 : CollatzResearch.WordTrace tailWord_4715649 prefixEnd_4715649 2421394534893925735300631 := by
  unfold tailWord_4715649
  simp only [CollatzResearch.WordTrace]
  refine ⟨171993848893016516575630001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114662565928677677717086667 171993848893016516575630001)
  ·
    refine ⟨128995386669762387431722501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171993848893016516575630001 128995386669762387431722501)
    ·
      refine ⟨24186635000580447643447969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128995386669762387431722501 24186635000580447643447969)
      ·
        refine ⟨18139976250435335732585977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24186635000580447643447969 18139976250435335732585977)
        ·
          refine ⟨13604982187826501799439483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18139976250435335732585977 13604982187826501799439483)
          ·
            refine ⟨20407473281739752699159225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13604982187826501799439483 20407473281739752699159225)
            ·
              refine ⟨15305604961304814524369419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20407473281739752699159225 15305604961304814524369419)
              ·
                refine ⟨22958407441957221786554129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15305604961304814524369419 22958407441957221786554129)
                ·
                  refine ⟨17218805581467916339915597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22958407441957221786554129 17218805581467916339915597)
                  ·
                    refine ⟨6457052093050468627468349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17218805581467916339915597 6457052093050468627468349)
                    ·
                      refine ⟨2421394534893925735300631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6457052093050468627468349 2421394534893925735300631)
                      ·
                        rfl

theorem cell23_4715649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_4715649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715649 prefixEnd_4715649 := by exact prefixLift 4715649
  have htrace : WordTrace (prefixWord ++ tailWord_4715649) baseStart_4715649 baseEnd_4715649 := by
    simpa [prefixWord, tailWord_4715649, baseEnd_4715649] using wordTrace_append hprefix tailTrace_4715649
  have hstable : (prefixWord ++ tailWord_4715649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715649).length < 2 ^ (prefixWord ++ tailWord_4715649).sum := by decide
  have hdescent : baseEnd_4715649 < baseStart_4715649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715652 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_4715652 : Nat := 118140960795 + 4715652 * 2 ^ 59
def prefixEnd_4715652 : Nat := 4983230072969 + 3 ^ 40 * 4715652 * 2
def baseEnd_4715652 : Nat := 807132025111963074521039

theorem tailTrace_4715652 : CollatzResearch.WordTrace tailWord_4715652 prefixEnd_4715652 807132025111963074521039 := by
  unfold tailWord_4715652
  simp only [CollatzResearch.WordTrace]
  refine ⟨85996979156002824043994605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114662638874670432058659473 85996979156002824043994605)
  ·
    refine ⟨32248867183501059016497977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85996979156002824043994605 32248867183501059016497977)
    ·
      refine ⟨24186650387625794262373483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32248867183501059016497977 24186650387625794262373483)
      ·
        refine ⟨36279975581438691393560225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24186650387625794262373483 36279975581438691393560225)
        ·
          refine ⟨27209981686079018545170169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36279975581438691393560225 27209981686079018545170169)
          ·
            refine ⟨20407486264559263908877627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27209981686079018545170169 20407486264559263908877627)
            ·
              refine ⟨30611229396838895863316441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20407486264559263908877627 30611229396838895863316441)
              ·
                refine ⟨22958422047629171897487331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30611229396838895863316441 22958422047629171897487331)
                ·
                  refine ⟨34437633071443757846230997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22958422047629171897487331 34437633071443757846230997)
                  ·
                    refine ⟨807132025111963074521039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34437633071443757846230997 807132025111963074521039)
                    ·
                      rfl

theorem cell23_4715652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_4715652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715652 prefixEnd_4715652 := by exact prefixLift 4715652
  have htrace : WordTrace (prefixWord ++ tailWord_4715652) baseStart_4715652 baseEnd_4715652 := by
    simpa [prefixWord, tailWord_4715652, baseEnd_4715652] using wordTrace_append hprefix tailTrace_4715652
  have hstable : (prefixWord ++ tailWord_4715652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715652).length < 2 ^ (prefixWord ++ tailWord_4715652).sum := by decide
  have hdescent : baseEnd_4715652 < baseStart_4715652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715675 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9]
def baseStart_4715675 : Nat := 118140960795 + 4715675 * 2 ^ 59
def prefixEnd_4715675 : Nat := 4983230072969 + 3 ^ 40 * 4715675 * 2
def baseEnd_4715675 : Nat := 2421407885390942633575511

theorem tailTrace_4715675 : CollatzResearch.WordTrace tailWord_4715675 prefixEnd_4715675 2421407885390942633575511 := by
  unfold tailWord_4715675
  simp only [CollatzResearch.WordTrace]
  refine ⟨171994797190922323016076479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114663198127281548677384319 171994797190922323016076479)
  ·
    refine ⟨257992195786383484524114719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171994797190922323016076479 257992195786383484524114719)
    ·
      refine ⟨386988293679575226786172079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257992195786383484524114719 386988293679575226786172079)
      ·
        refine ⟨580482440519362840179258119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386988293679575226786172079 580482440519362840179258119)
        ·
          refine ⟨870723660779044260268887179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580482440519362840179258119 870723660779044260268887179)
          ·
            refine ⟨1306085491168566390403330769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870723660779044260268887179 1306085491168566390403330769)
            ·
              refine ⟨979564118376424792802498077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306085491168566390403330769 979564118376424792802498077)
              ·
                refine ⟨367336544391159297300936779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 979564118376424792802498077 367336544391159297300936779)
                ·
                  refine ⟨551004816586738945951405169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367336544391159297300936779 551004816586738945951405169)
                  ·
                    refine ⟨413253612440054209463553877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 551004816586738945951405169 413253612440054209463553877)
                    ·
                      refine ⟨2421407885390942633575511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 413253612440054209463553877 2421407885390942633575511)
                      ·
                        rfl

theorem cell23_4715675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_4715675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715675 prefixEnd_4715675 := by exact prefixLift 4715675
  have htrace : WordTrace (prefixWord ++ tailWord_4715675) baseStart_4715675 baseEnd_4715675 := by
    simpa [prefixWord, tailWord_4715675, baseEnd_4715675] using wordTrace_append hprefix tailTrace_4715675
  have hstable : (prefixWord ++ tailWord_4715675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715675).length < 2 ^ (prefixWord ++ tailWord_4715675).sum := by decide
  have hdescent : baseEnd_4715675 < baseStart_4715675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715692 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_4715692 : Nat := 118140960795 + 4715692 * 2 ^ 59
def prefixEnd_4715692 : Nat := 4983230072969 + 3 ^ 40 * 4715692 * 2
def baseEnd_4715692 : Nat := 2421416614562069067062933

theorem tailTrace_4715692 : CollatzResearch.WordTrace tailWord_4715692 prefixEnd_4715692 2421416614562069067062933 := by
  unfold tailWord_4715692
  simp only [CollatzResearch.WordTrace]
  refine ⟨85997708615930367459722665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114663611487907156612963553 85997708615930367459722665)
  ·
    refine ⟨64498281461947775594791999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85997708615930367459722665 64498281461947775594791999)
    ·
      refine ⟨96747422192921663392187999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64498281461947775594791999 96747422192921663392187999)
      ·
        refine ⟨145121133289382495088281999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96747422192921663392187999 145121133289382495088281999)
        ·
          refine ⟨217681699934073742632422999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145121133289382495088281999 217681699934073742632422999)
          ·
            refine ⟨326522549901110613948634499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217681699934073742632422999 326522549901110613948634499)
            ·
              refine ⟨489783824851665920922951749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326522549901110613948634499 489783824851665920922951749)
              ·
                refine ⟨91834467159687360173053453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489783824851665920922951749 91834467159687360173053453)
                ·
                  refine ⟨34437925184882760064895045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91834467159687360173053453 34437925184882760064895045)
                  ·
                    refine ⟨6457110972165517512167821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34437925184882760064895045 6457110972165517512167821)
                    ·
                      refine ⟨2421416614562069067062933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6457110972165517512167821 2421416614562069067062933)
                      ·
                        rfl

theorem cell23_4715692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_4715692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715692 prefixEnd_4715692 := by exact prefixLift 4715692
  have htrace : WordTrace (prefixWord ++ tailWord_4715692) baseStart_4715692 baseEnd_4715692 := by
    simpa [prefixWord, tailWord_4715692, baseEnd_4715692] using wordTrace_append hprefix tailTrace_4715692
  have hstable : (prefixWord ++ tailWord_4715692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715692).length < 2 ^ (prefixWord ++ tailWord_4715692).sum := by decide
  have hdescent : baseEnd_4715692 < baseStart_4715692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715699 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 3, 4]
def baseStart_4715699 : Nat := 118140960795 + 4715699 * 2 ^ 59
def prefixEnd_4715699 : Nat := 4983230072969 + 3 ^ 40 * 4715699 * 2
def baseEnd_4715699 : Nat := 807140069642216846558467

theorem tailTrace_4715699 : CollatzResearch.WordTrace tailWord_4715699 prefixEnd_4715699 807140069642216846558467 := by
  unfold tailWord_4715699
  simp only [CollatzResearch.WordTrace]
  refine ⟨171995672542835375114950151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114663781695223583409966767 171995672542835375114950151)
  ·
    refine ⟨257993508814253062672425227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171995672542835375114950151 257993508814253062672425227)
    ·
      refine ⟨386990263221379594008637841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257993508814253062672425227 386990263221379594008637841)
      ·
        refine ⟨290242697416034695506478381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386990263221379594008637841 290242697416034695506478381)
        ·
          refine ⟨108841011531013010814929393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290242697416034695506478381 108841011531013010814929393)
          ·
            refine ⟨81630758648259758111197045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108841011531013010814929393 81630758648259758111197045)
            ·
              refine ⟨7652883623274352322924723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81630758648259758111197045 7652883623274352322924723)
              ·
                refine ⟨11479325434911528484387085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7652883623274352322924723 11479325434911528484387085)
                ·
                  refine ⟨4304747038091823181645157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11479325434911528484387085 4304747038091823181645157)
                  ·
                    refine ⟨807140069642216846558467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304747038091823181645157 807140069642216846558467)
                    ·
                      rfl

theorem cell23_4715699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 4].length) (baseStart_4715699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715699 prefixEnd_4715699 := by exact prefixLift 4715699
  have htrace : WordTrace (prefixWord ++ tailWord_4715699) baseStart_4715699 baseEnd_4715699 := by
    simpa [prefixWord, tailWord_4715699, baseEnd_4715699] using wordTrace_append hprefix tailTrace_4715699
  have hstable : (prefixWord ++ tailWord_4715699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715699).length < 2 ^ (prefixWord ++ tailWord_4715699).sum := by decide
  have hdescent : baseEnd_4715699 < baseStart_4715699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715766 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_4715766 : Nat := 118140960795 + 4715766 * 2 ^ 59
def prefixEnd_4715766 : Nat := 4983230072969 + 3 ^ 40 * 4715766 * 2
def baseEnd_4715766 : Nat := 2421454612130501777537593

theorem tailTrace_4715766 : CollatzResearch.WordTrace tailWord_4715766 prefixEnd_4715766 2421454612130501777537593 := by
  unfold tailWord_4715766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10749882264599540347352447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114665410822395097038426101 10749882264599540347352447)
  ·
    refine ⟨16124823396899310521028671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10749882264599540347352447 16124823396899310521028671)
    ·
      refine ⟨24187235095348965781543007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16124823396899310521028671 24187235095348965781543007)
      ·
        refine ⟨36280852643023448672314511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24187235095348965781543007 36280852643023448672314511)
        ·
          refine ⟨54421278964535173008471767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36280852643023448672314511 54421278964535173008471767)
          ·
            refine ⟨81631918446802759512707651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54421278964535173008471767 81631918446802759512707651)
            ·
              refine ⟨122447877670204139269061477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81631918446802759512707651 122447877670204139269061477)
              ·
                refine ⟨22958977063163276112949027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122447877670204139269061477 22958977063163276112949027)
                ·
                  refine ⟨34438465594744914169423541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22958977063163276112949027 34438465594744914169423541)
                  ·
                    refine ⟨3228606149507335703383457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34438465594744914169423541 3228606149507335703383457)
                    ·
                      refine ⟨2421454612130501777537593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228606149507335703383457 2421454612130501777537593)
                      ·
                        rfl

theorem cell23_4715766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_4715766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715766 prefixEnd_4715766 := by exact prefixLift 4715766
  have htrace : WordTrace (prefixWord ++ tailWord_4715766) baseStart_4715766 baseEnd_4715766 := by
    simpa [prefixWord, tailWord_4715766, baseEnd_4715766] using wordTrace_append hprefix tailTrace_4715766
  have hstable : (prefixWord ++ tailWord_4715766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715766).length < 2 ^ (prefixWord ++ tailWord_4715766).sum := by decide
  have hdescent : baseEnd_4715766 < baseStart_4715766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715779 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 4]
def baseStart_4715779 : Nat := 118140960795 + 4715779 * 2 ^ 59
def prefixEnd_4715779 : Nat := 4983230072969 + 3 ^ 40 * 4715779 * 2
def baseEnd_4715779 : Nat := 2421461287379010226675033

theorem tailTrace_4715779 : CollatzResearch.WordTrace tailWord_4715779 prefixEnd_4715779 2421461287379010226675033 := by
  unfold tailWord_4715779
  simp only [CollatzResearch.WordTrace]
  refine ⟨171998590382545548777862391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114665726921697032518574927 171998590382545548777862391)
  ·
    refine ⟨257997885573818323166793587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171998590382545548777862391 257997885573818323166793587)
    ·
      refine ⟨386996828360727484750190381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257997885573818323166793587 386996828360727484750190381)
      ·
        refine ⟨145123810635272806781321393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386996828360727484750190381 145123810635272806781321393)
        ·
          refine ⟨108842857976454605085991045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145123810635272806781321393 108842857976454605085991045)
          ·
            refine ⟨20408035870585238453623321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108842857976454605085991045 20408035870585238453623321)
            ·
              refine ⟨15306026902938928840217491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20408035870585238453623321 15306026902938928840217491)
              ·
                refine ⟨22959040354408393260326237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15306026902938928840217491 22959040354408393260326237)
                ·
                  refine ⟨8609640132903147472622339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22959040354408393260326237 8609640132903147472622339)
                  ·
                    refine ⟨12914460199354721208933509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8609640132903147472622339 12914460199354721208933509)
                    ·
                      refine ⟨2421461287379010226675033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12914460199354721208933509 2421461287379010226675033)
                      ·
                        rfl

theorem cell23_4715779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_4715779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715779 prefixEnd_4715779 := by exact prefixLift 4715779
  have htrace : WordTrace (prefixWord ++ tailWord_4715779) baseStart_4715779 baseEnd_4715779 := by
    simpa [prefixWord, tailWord_4715779, baseEnd_4715779] using wordTrace_append hprefix tailTrace_4715779
  have hstable : (prefixWord ++ tailWord_4715779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715779).length < 2 ^ (prefixWord ++ tailWord_4715779).sum := by decide
  have hdescent : baseEnd_4715779 < baseStart_4715779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715790 : List Nat := [4, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_4715790 : Nat := 118140960795 + 4715790 * 2 ^ 59
def prefixEnd_4715790 : Nat := 4983230072969 + 3 ^ 40 * 4715790 * 2
def baseEnd_4715790 : Nat := 2421466935666209683637483

theorem tailTrace_4715790 : CollatzResearch.WordTrace tailWord_4715790 prefixEnd_4715790 2421466935666209683637483 := by
  unfold tailWord_4715790
  simp only [CollatzResearch.WordTrace]
  refine ⟨21499873948188212207064103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114665994390337131771008549 21499873948188212207064103)
  ·
    refine ⟨32249810922282318310596155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21499873948188212207064103 32249810922282318310596155)
    ·
      refine ⟨48374716383423477465894233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32249810922282318310596155 48374716383423477465894233)
      ·
        refine ⟨36281037287567608099420675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48374716383423477465894233 36281037287567608099420675)
        ·
          refine ⟨54421555931351412149131013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36281037287567608099420675 54421555931351412149131013)
          ·
            refine ⟨10204041737128389777962065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54421555931351412149131013 10204041737128389777962065)
            ·
              refine ⟨7653031302846292333471549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10204041737128389777962065 7653031302846292333471549)
              ·
                refine ⟨2869886738567359625051831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7653031302846292333471549 2869886738567359625051831)
                ·
                  refine ⟨4304830107851039437577747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869886738567359625051831 4304830107851039437577747)
                  ·
                    refine ⟨6457245161776559156366621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4304830107851039437577747 6457245161776559156366621)
                    ·
                      refine ⟨2421466935666209683637483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6457245161776559156366621 2421466935666209683637483)
                      ·
                        rfl

theorem cell23_4715790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_4715790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715790 prefixEnd_4715790 := by exact prefixLift 4715790
  have htrace : WordTrace (prefixWord ++ tailWord_4715790) baseStart_4715790 baseEnd_4715790 := by
    simpa [prefixWord, tailWord_4715790, baseEnd_4715790] using wordTrace_append hprefix tailTrace_4715790
  have hstable : (prefixWord ++ tailWord_4715790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715790).length < 2 ^ (prefixWord ++ tailWord_4715790).sum := by decide
  have hdescent : baseEnd_4715790 < baseStart_4715790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715792 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_4715792 : Nat := 118140960795 + 4715792 * 2 ^ 59
def prefixEnd_4715792 : Nat := 4983230072969 + 3 ^ 40 * 4715792 * 2
def baseEnd_4715792 : Nat := 2421467962627518675812473

theorem tailTrace_4715792 : CollatzResearch.WordTrace tailWord_4715792 prefixEnd_4715792 2421467962627518675812473 := by
  unfold tailWord_4715792
  simp only [CollatzResearch.WordTrace]
  refine ⟨85999532265749225999042815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114666043020998967998723753 85999532265749225999042815)
  ·
    refine ⟨128999298398623838998564223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85999532265749225999042815 128999298398623838998564223)
    ·
      refine ⟨193498947597935758497846335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128999298398623838998564223 193498947597935758497846335)
      ·
        refine ⟨290248421396903637746769503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193498947597935758497846335 290248421396903637746769503)
        ·
          refine ⟨435372632095355456620154255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290248421396903637746769503 435372632095355456620154255)
          ·
            refine ⟨653058948143033184930231383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435372632095355456620154255 653058948143033184930231383)
            ·
              refine ⟨979588422214549777395347075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653058948143033184930231383 979588422214549777395347075)
              ·
                refine ⟨1469382633321824666093020613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979588422214549777395347075 1469382633321824666093020613)
                ·
                  refine ⟨275509243747842124892441365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469382633321824666093020613 275509243747842124892441365)
                  ·
                    refine ⟨12914495800680099604333189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 275509243747842124892441365 12914495800680099604333189)
                    ·
                      refine ⟨2421467962627518675812473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12914495800680099604333189 2421467962627518675812473)
                      ·
                        rfl

theorem cell23_4715792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_4715792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715792 prefixEnd_4715792 := by exact prefixLift 4715792
  have htrace : WordTrace (prefixWord ++ tailWord_4715792) baseStart_4715792 baseEnd_4715792 := by
    simpa [prefixWord, tailWord_4715792, baseEnd_4715792] using wordTrace_append hprefix tailTrace_4715792
  have hstable : (prefixWord ++ tailWord_4715792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715792).length < 2 ^ (prefixWord ++ tailWord_4715792).sum := by decide
  have hdescent : baseEnd_4715792 < baseStart_4715792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715799 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4715799 : Nat := 118140960795 + 4715799 * 2 ^ 59
def prefixEnd_4715799 : Nat := 4983230072969 + 3 ^ 40 * 4715799 * 2
def baseEnd_4715799 : Nat := 2421471556992100148424941

theorem tailTrace_4715799 : CollatzResearch.WordTrace tailWord_4715799 prefixEnd_4715799 2421471556992100148424941 := by
  unfold tailWord_4715799
  simp only [CollatzResearch.WordTrace]
  refine ⟨171999319842473092193590451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114666213228315394795726967 171999319842473092193590451)
  ·
    refine ⟨257998979763709638290385677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171999319842473092193590451 257998979763709638290385677)
    ·
      refine ⟨96749617411391114358894629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257998979763709638290385677 96749617411391114358894629)
      ·
        refine ⟨18140553264635833942292743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96749617411391114358894629 18140553264635833942292743)
        ·
          refine ⟨27210829896953750913439115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18140553264635833942292743 27210829896953750913439115)
          ·
            refine ⟨40816244845430626370158673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27210829896953750913439115 40816244845430626370158673)
            ·
              refine ⟨30612183634072969777619005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40816244845430626370158673 30612183634072969777619005)
              ·
                refine ⟨11479568862777363666607127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30612183634072969777619005 11479568862777363666607127)
                ·
                  refine ⟨17219353294166045499910691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11479568862777363666607127 17219353294166045499910691)
                  ·
                    refine ⟨25829029941249068249866037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17219353294166045499910691 25829029941249068249866037)
                    ·
                      refine ⟨2421471556992100148424941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25829029941249068249866037 2421471556992100148424941)
                      ·
                        rfl

theorem cell23_4715799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4715799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715799 prefixEnd_4715799 := by exact prefixLift 4715799
  have htrace : WordTrace (prefixWord ++ tailWord_4715799) baseStart_4715799 baseEnd_4715799 := by
    simpa [prefixWord, tailWord_4715799, baseEnd_4715799] using wordTrace_append hprefix tailTrace_4715799
  have hstable : (prefixWord ++ tailWord_4715799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715799).length < 2 ^ (prefixWord ++ tailWord_4715799).sum := by decide
  have hdescent : baseEnd_4715799 < baseStart_4715799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715813 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 3, 2, 2]
def baseStart_4715813 : Nat := 118140960795 + 4715813 * 2 ^ 59
def prefixEnd_4715813 : Nat := 4983230072969 + 3 ^ 40 * 4715813 * 2
def baseEnd_4715813 : Nat := 2421478745721263093649877

theorem tailTrace_4715813 : CollatzResearch.WordTrace tailWord_4715813 prefixEnd_4715813 2421478745721263093649877 := by
  unfold tailWord_4715813
  simp only [CollatzResearch.WordTrace]
  refine ⟨171999830464422372584600093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114666553642948248389733395 171999830464422372584600093)
  ·
    refine ⟨64499936424158389719225035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171999830464422372584600093 64499936424158389719225035)
    ·
      refine ⟨96749904636237584578837553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64499936424158389719225035 96749904636237584578837553)
      ·
        refine ⟨72562428477178188434128165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96749904636237584578837553 72562428477178188434128165)
        ·
          refine ⟨13605455339470910331399031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72562428477178188434128165 13605455339470910331399031)
          ·
            refine ⟨20408183009206365497098547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13605455339470910331399031 20408183009206365497098547)
            ·
              refine ⟨30612274513809548245647821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20408183009206365497098547 30612274513809548245647821)
              ·
                refine ⟨11479602942678580592117933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30612274513809548245647821 11479602942678580592117933)
                ·
                  refine ⟨4304851103504467722044225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11479602942678580592117933 4304851103504467722044225)
                  ·
                    refine ⟨3228638327628350791533169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4304851103504467722044225 3228638327628350791533169)
                    ·
                      refine ⟨2421478745721263093649877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228638327628350791533169 2421478745721263093649877)
                      ·
                        rfl

theorem cell23_4715813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_4715813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715813 prefixEnd_4715813 := by exact prefixLift 4715813
  have htrace : WordTrace (prefixWord ++ tailWord_4715813) baseStart_4715813 baseEnd_4715813 := by
    simpa [prefixWord, tailWord_4715813, baseEnd_4715813] using wordTrace_append hprefix tailTrace_4715813
  have hstable : (prefixWord ++ tailWord_4715813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715813).length < 2 ^ (prefixWord ++ tailWord_4715813).sum := by decide
  have hdescent : baseEnd_4715813 < baseStart_4715813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715816 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4715816 : Nat := 118140960795 + 4715816 * 2 ^ 59
def prefixEnd_4715816 : Nat := 4983230072969 + 3 ^ 40 * 4715816 * 2
def baseEnd_4715816 : Nat := 2421480286163226581912363

theorem tailTrace_4715816 : CollatzResearch.WordTrace tailWord_4715816 prefixEnd_4715816 2421480286163226581912363 := by
  unfold tailWord_4715816
  simp only [CollatzResearch.WordTrace]
  refine ⟨85999969941705752048479651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114666626588941002731306201 85999969941705752048479651)
  ·
    refine ⟨128999954912558628072719477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85999969941705752048479651 128999954912558628072719477)
    ·
      refine ⟨12093745773052371381817451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128999954912558628072719477 12093745773052371381817451)
      ·
        refine ⟨18140618659578557072726177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12093745773052371381817451 18140618659578557072726177)
        ·
          refine ⟨13605463994683917804544633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18140618659578557072726177 13605463994683917804544633)
          ·
            refine ⟨10204097996012938353408475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13605463994683917804544633 10204097996012938353408475)
            ·
              refine ⟨15306146994019407530112713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10204097996012938353408475 15306146994019407530112713)
              ·
                refine ⟨11479610245514555647584535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15306146994019407530112713 11479610245514555647584535)
                ·
                  refine ⟨17219415368271833471376803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11479610245514555647584535 17219415368271833471376803)
                  ·
                    refine ⟨25829123052407750207065205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17219415368271833471376803 25829123052407750207065205)
                    ·
                      refine ⟨2421480286163226581912363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25829123052407750207065205 2421480286163226581912363)
                      ·
                        rfl

theorem cell23_4715816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4715816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715816 prefixEnd_4715816 := by exact prefixLift 4715816
  have htrace : WordTrace (prefixWord ++ tailWord_4715816) baseStart_4715816 baseEnd_4715816 := by
    simpa [prefixWord, tailWord_4715816, baseEnd_4715816] using wordTrace_append hprefix tailTrace_4715816
  have hstable : (prefixWord ++ tailWord_4715816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715816).length < 2 ^ (prefixWord ++ tailWord_4715816).sum := by decide
  have hdescent : baseEnd_4715816 < baseStart_4715816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715826 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_4715826 : Nat := 118140960795 + 4715826 * 2 ^ 59
def prefixEnd_4715826 : Nat := 4983230072969 + 3 ^ 40 * 4715826 * 2
def baseEnd_4715826 : Nat := 2421485420969771542787317

theorem tailTrace_4715826 : CollatzResearch.WordTrace tailWord_4715826 prefixEnd_4715826 2421485420969771542787317 := by
  unfold tailWord_4715826
  simp only [CollatzResearch.WordTrace]
  refine ⟨43000076153343818951205833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114666869742250183869882221 43000076153343818951205833)
  ·
    refine ⟨32250057115007864213404375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43000076153343818951205833 32250057115007864213404375)
    ·
      refine ⟨48375085672511796320106563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32250057115007864213404375 48375085672511796320106563)
      ·
        refine ⟨72562628508767694480159845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48375085672511796320106563 72562628508767694480159845)
        ·
          refine ⟨13605492845393942715029971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72562628508767694480159845 13605492845393942715029971)
          ·
            refine ⟨20408239268090914072544957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13605492845393942715029971 20408239268090914072544957)
            ·
              refine ⟨7653089725534092777204359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20408239268090914072544957 7653089725534092777204359)
              ·
                refine ⟨11479634588301139165806539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7653089725534092777204359 11479634588301139165806539)
                ·
                  refine ⟨17219451882451708748709809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11479634588301139165806539 17219451882451708748709809)
                  ·
                    refine ⟨12914588911838781561532357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17219451882451708748709809 12914588911838781561532357)
                    ·
                      refine ⟨2421485420969771542787317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12914588911838781561532357 2421485420969771542787317)
                      ·
                        rfl

theorem cell23_4715826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_4715826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715826 prefixEnd_4715826 := by exact prefixLift 4715826
  have htrace : WordTrace (prefixWord ++ tailWord_4715826) baseStart_4715826 baseEnd_4715826 := by
    simpa [prefixWord, tailWord_4715826, baseEnd_4715826] using wordTrace_append hprefix tailTrace_4715826
  have hstable : (prefixWord ++ tailWord_4715826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715826).length < 2 ^ (prefixWord ++ tailWord_4715826).sum := by decide
  have hdescent : baseEnd_4715826 < baseStart_4715826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715836 : List Nat := [2, 2, 2, 2, 1, 5, 2, 7]
def baseStart_4715836 : Nat := 118140960795 + 4715836 * 2 ^ 59
def prefixEnd_4715836 : Nat := 4983230072969 + 3 ^ 40 * 4715836 * 2
def baseEnd_4715836 : Nat := 89684835399122833468973

theorem tailTrace_4715836 : CollatzResearch.WordTrace tailWord_4715836 prefixEnd_4715836 89684835399122833468973 := by
  unfold tailWord_4715836
  simp only [CollatzResearch.WordTrace]
  refine ⟨86000334671669523756343681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114667112895559365008458241 86000334671669523756343681)
  ·
    refine ⟨64500251003752142817257761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86000334671669523756343681 64500251003752142817257761)
    ·
      refine ⟨48375188252814107112943321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64500251003752142817257761 48375188252814107112943321)
      ·
        refine ⟨36281391189610580334707491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48375188252814107112943321 36281391189610580334707491)
        ·
          refine ⟨54422086784415870502061237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36281391189610580334707491 54422086784415870502061237)
          ·
            refine ⟨5102070636038987859568241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54422086784415870502061237 5102070636038987859568241)
            ·
              refine ⟨3826552977029240894676181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5102070636038987859568241 3826552977029240894676181)
              ·
                refine ⟨89684835399122833468973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3826552977029240894676181 89684835399122833468973)
                ·
                  rfl

theorem cell23_4715836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 7].length) (baseStart_4715836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715836 prefixEnd_4715836 := by exact prefixLift 4715836
  have htrace : WordTrace (prefixWord ++ tailWord_4715836) baseStart_4715836 baseEnd_4715836 := by
    simpa [prefixWord, tailWord_4715836, baseEnd_4715836] using wordTrace_append hprefix tailTrace_4715836
  have hstable : (prefixWord ++ tailWord_4715836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715836).length < 2 ^ (prefixWord ++ tailWord_4715836).sum := by decide
  have hdescent : baseEnd_4715836 < baseStart_4715836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715847 : List Nat := [1, 1, 4, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_4715847 : Nat := 118140960795 + 4715847 * 2 ^ 59
def prefixEnd_4715847 : Nat := 4983230072969 + 3 ^ 40 * 4715847 * 2
def baseEnd_4715847 : Nat := 2421496204063515960624721

theorem tailTrace_4715847 : CollatzResearch.WordTrace tailWord_4715847 prefixEnd_4715847 2421496204063515960624721 := by
  unfold tailWord_4715847
  simp only [CollatzResearch.WordTrace]
  refine ⟨172001070546299196391337795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114667380364199464260891863 172001070546299196391337795)
  ·
    refine ⟨258001605819448794587006693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172001070546299196391337795 258001605819448794587006693)
    ·
      refine ⟨48375301091146648985063755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258001605819448794587006693 48375301091146648985063755)
      ·
        refine ⟨72562951636719973477595633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48375301091146648985063755 72562951636719973477595633)
        ·
          refine ⟨54422213727539980108196725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72562951636719973477595633 54422213727539980108196725)
          ·
            refine ⟨5102082536956873135143443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54422213727539980108196725 5102082536956873135143443)
            ·
              refine ⟨7653123805435309702715165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102082536956873135143443 7653123805435309702715165)
              ·
                refine ⟨2869921427038241138518187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7653123805435309702715165 2869921427038241138518187)
                ·
                  refine ⟨4304882140557361707777281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869921427038241138518187 4304882140557361707777281)
                  ·
                    refine ⟨3228661605418021280832961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4304882140557361707777281 3228661605418021280832961)
                    ·
                      refine ⟨2421496204063515960624721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228661605418021280832961 2421496204063515960624721)
                      ·
                        rfl

theorem cell23_4715847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_4715847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715847 prefixEnd_4715847 := by exact prefixLift 4715847
  have htrace : WordTrace (prefixWord ++ tailWord_4715847) baseStart_4715847 baseEnd_4715847 := by
    simpa [prefixWord, tailWord_4715847, baseEnd_4715847] using wordTrace_append hprefix tailTrace_4715847
  have hstable : (prefixWord ++ tailWord_4715847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715847).length < 2 ^ (prefixWord ++ tailWord_4715847).sum := by decide
  have hdescent : baseEnd_4715847 < baseStart_4715847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715853 : List Nat := [1, 6, 1, 3, 1, 2, 9]
def baseStart_4715853 : Nat := 118140960795 + 4715853 * 2 ^ 59
def prefixEnd_4715853 : Nat := 4983230072969 + 3 ^ 40 * 4715853 * 2
def baseEnd_4715853 : Nat := 29895052900585715273453

theorem tailTrace_4715853 : CollatzResearch.WordTrace tailWord_4715853 prefixEnd_4715853 29895052900585715273453 := by
  unfold tailWord_4715853
  simp only [CollatzResearch.WordTrace]
  refine ⟨172001289384277459416056213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114667526256184972944037475 172001289384277459416056213)
  ·
    refine ⟨8062560439888005910127635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172001289384277459416056213 8062560439888005910127635)
    ·
      refine ⟨12093840659832008865191453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8062560439888005910127635 12093840659832008865191453)
      ·
        refine ⟨4535190247437003324446795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12093840659832008865191453 4535190247437003324446795)
        ·
          refine ⟨6802785371155504986670193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4535190247437003324446795 6802785371155504986670193)
          ·
            refine ⟨5102089028366628740002645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6802785371155504986670193 5102089028366628740002645)
            ·
              refine ⟨29895052900585715273453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5102089028366628740002645 29895052900585715273453)
              ·
                rfl

theorem cell23_4715853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 9].length) (baseStart_4715853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715853 prefixEnd_4715853 := by exact prefixLift 4715853
  have htrace : WordTrace (prefixWord ++ tailWord_4715853) baseStart_4715853 baseEnd_4715853 := by
    simpa [prefixWord, tailWord_4715853, baseEnd_4715853] using wordTrace_append hprefix tailTrace_4715853
  have hstable : (prefixWord ++ tailWord_4715853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715853).length < 2 ^ (prefixWord ++ tailWord_4715853).sum := by decide
  have hdescent : baseEnd_4715853 < baseStart_4715853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715880 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4715880 : Nat := 118140960795 + 4715880 * 2 ^ 59
def prefixEnd_4715880 : Nat := 4983230072969 + 3 ^ 40 * 4715880 * 2
def baseEnd_4715880 : Nat := 2421513148925114331512069

theorem tailTrace_4715880 : CollatzResearch.WordTrace tailWord_4715880 prefixEnd_4715880 2421513148925114331512069 := by
  unfold tailWord_4715880
  simp only [CollatzResearch.WordTrace]
  refine ⟨86001137077589821513644547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114668182770119762018192729 86001137077589821513644547)
  ·
    refine ⟨129001705616384732270466821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86001137077589821513644547 129001705616384732270466821)
    ·
      refine ⟨24187819803072137300712529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129001705616384732270466821 24187819803072137300712529)
      ·
        refine ⟨18140864852304102975534397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24187819803072137300712529 18140864852304102975534397)
        ·
          refine ⟨6802824319614038615825399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18140864852304102975534397 6802824319614038615825399)
          ·
            refine ⟨10204236479421057923738099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6802824319614038615825399 10204236479421057923738099)
            ·
              refine ⟨15306354719131586885607149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10204236479421057923738099 15306354719131586885607149)
              ·
                refine ⟨5739883019674345082102681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15306354719131586885607149 5739883019674345082102681)
                ·
                  refine ⟨4304912264755758811577011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5739883019674345082102681 4304912264755758811577011)
                  ·
                    refine ⟨6457368397133638217365517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4304912264755758811577011 6457368397133638217365517)
                    ·
                      refine ⟨2421513148925114331512069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6457368397133638217365517 2421513148925114331512069)
                      ·
                        rfl

theorem cell23_4715880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4715880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715880 prefixEnd_4715880 := by exact prefixLift 4715880
  have htrace : WordTrace (prefixWord ++ tailWord_4715880) baseStart_4715880 baseEnd_4715880 := by
    simpa [prefixWord, tailWord_4715880, baseEnd_4715880] using wordTrace_append hprefix tailTrace_4715880
  have hstable : (prefixWord ++ tailWord_4715880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715880).length < 2 ^ (prefixWord ++ tailWord_4715880).sum := by decide
  have hdescent : baseEnd_4715880 < baseStart_4715880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715889 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_4715889 : Nat := 118140960795 + 4715889 * 2 ^ 59
def prefixEnd_4715889 : Nat := 4983230072969 + 3 ^ 40 * 4715889 * 2
def baseEnd_4715889 : Nat := 2421517770251004796299527

theorem tailTrace_4715889 : CollatzResearch.WordTrace tailWord_4715889 prefixEnd_4715889 2421517770251004796299527 := by
  unfold tailWord_4715889
  simp only [CollatzResearch.WordTrace]
  refine ⟨172002602412147037564366721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114668401608098025042911147 172002602412147037564366721)
  ·
    refine ⟨129001951809110278173275041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172002602412147037564366721 129001951809110278173275041)
    ·
      refine ⟨96751463856832708629956281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129001951809110278173275041 96751463856832708629956281)
      ·
        refine ⟨72563597892624531472467211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96751463856832708629956281 72563597892624531472467211)
        ·
          refine ⟨108845396838936797208700817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72563597892624531472467211 108845396838936797208700817)
          ·
            refine ⟨81634047629202597906525613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108845396838936797208700817 81634047629202597906525613)
            ·
              refine ⟨30612767860950974214947105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81634047629202597906525613 30612767860950974214947105)
              ·
                refine ⟨22959575895713230661210329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30612767860950974214947105 22959575895713230661210329)
                ·
                  refine ⟨17219681921784922995907747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22959575895713230661210329 17219681921784922995907747)
                  ·
                    refine ⟨25829522882677384493861621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17219681921784922995907747 25829522882677384493861621)
                    ·
                      refine ⟨2421517770251004796299527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25829522882677384493861621 2421517770251004796299527)
                      ·
                        rfl

theorem cell23_4715889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_4715889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715889 prefixEnd_4715889 := by exact prefixLift 4715889
  have htrace : WordTrace (prefixWord ++ tailWord_4715889) baseStart_4715889 baseEnd_4715889 := by
    simpa [prefixWord, tailWord_4715889, baseEnd_4715889] using wordTrace_append hprefix tailTrace_4715889
  have hstable : (prefixWord ++ tailWord_4715889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715889).length < 2 ^ (prefixWord ++ tailWord_4715889).sum := by decide
  have hdescent : baseEnd_4715889 < baseStart_4715889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715936 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3]
def baseStart_4715936 : Nat := 118140960795 + 4715936 * 2 ^ 59
def prefixEnd_4715936 : Nat := 4983230072969 + 3 ^ 40 * 4715936 * 2
def baseEnd_4715936 : Nat := 2421541903841766112411811

theorem tailTrace_4715936 : CollatzResearch.WordTrace tailWord_4715936 prefixEnd_4715936 2421541903841766112411811 := by
  unfold tailWord_4715936
  simp only [CollatzResearch.WordTrace]
  refine ⟨86002158321488382295663831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114669544428651176394218441 86002158321488382295663831)
  ·
    refine ⟨129003237482232573443495747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86002158321488382295663831 129003237482232573443495747)
    ·
      refine ⟨193504856223348860165243621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129003237482232573443495747 193504856223348860165243621)
      ·
        refine ⟨36282160541877911280983179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193504856223348860165243621 36282160541877911280983179)
        ·
          refine ⟨54423240812816866921474769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36282160541877911280983179 54423240812816866921474769)
          ·
            refine ⟨40817430609612650191106077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54423240812816866921474769 40817430609612650191106077)
            ·
              refine ⟨15306536478604743821664779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40817430609612650191106077 15306536478604743821664779)
              ·
                refine ⟨22959804717907115732497169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15306536478604743821664779 22959804717907115732497169)
                ·
                  refine ⟨17219853538430336799372877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22959804717907115732497169 17219853538430336799372877)
                  ·
                    refine ⟨6457445076911376299764829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17219853538430336799372877 6457445076911376299764829)
                    ·
                      refine ⟨2421541903841766112411811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6457445076911376299764829 2421541903841766112411811)
                      ·
                        rfl

theorem cell23_4715936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_4715936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715936 prefixEnd_4715936 := by exact prefixLift 4715936
  have htrace : WordTrace (prefixWord ++ tailWord_4715936) baseStart_4715936 baseEnd_4715936 := by
    simpa [prefixWord, tailWord_4715936, baseEnd_4715936] using wordTrace_append hprefix tailTrace_4715936
  have hstable : (prefixWord ++ tailWord_4715936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715936).length < 2 ^ (prefixWord ++ tailWord_4715936).sum := by decide
  have hdescent : baseEnd_4715936 < baseStart_4715936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715939 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 1, 7]
def baseStart_4715939 : Nat := 118140960795 + 4715939 * 2 ^ 59
def prefixEnd_4715939 : Nat := 4983230072969 + 3 ^ 40 * 4715939 * 2
def baseEnd_4715939 : Nat := 807181148094576533558099

theorem tailTrace_4715939 : CollatzResearch.WordTrace tailWord_4715939 prefixEnd_4715939 807181148094576533558099 := by
  unfold tailWord_4715939
  simp only [CollatzResearch.WordTrace]
  refine ⟨172004426061965896103686871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114669617374643930735791247 172004426061965896103686871)
  ·
    refine ⟨258006639092948844155530307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172004426061965896103686871 258006639092948844155530307)
    ·
      refine ⟨387009958639423266233295461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258006639092948844155530307 387009958639423266233295461)
      ·
        refine ⟨72564367244891862418742899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387009958639423266233295461 72564367244891862418742899)
        ·
          refine ⟨108846550867337793628114349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72564367244891862418742899 108846550867337793628114349)
          ·
            refine ⟨40817456575251672610542881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108846550867337793628114349 40817456575251672610542881)
            ·
              refine ⟨30613092431438754457907161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40817456575251672610542881 30613092431438754457907161)
              ·
                refine ⟨22959819323579065843430371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30613092431438754457907161 22959819323579065843430371)
                ·
                  refine ⟨34439728985368598765145557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22959819323579065843430371 34439728985368598765145557)
                  ·
                    refine ⟨807181148094576533558099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34439728985368598765145557 807181148094576533558099)
                    ·
                      rfl

theorem cell23_4715939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 7].length) (baseStart_4715939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715939 prefixEnd_4715939 := by exact prefixLift 4715939
  have htrace : WordTrace (prefixWord ++ tailWord_4715939) baseStart_4715939 baseEnd_4715939 := by
    simpa [prefixWord, tailWord_4715939, baseEnd_4715939] using wordTrace_append hprefix tailTrace_4715939
  have hstable : (prefixWord ++ tailWord_4715939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715939).length < 2 ^ (prefixWord ++ tailWord_4715939).sum := by decide
  have hdescent : baseEnd_4715939 < baseStart_4715939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715976 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_4715976 : Nat := 118140960795 + 4715976 * 2 ^ 59
def prefixEnd_4715976 : Nat := 4983230072969 + 3 ^ 40 * 4715976 * 2
def baseEnd_4715976 : Nat := 2421562443067945955911627

theorem tailTrace_4715976 : CollatzResearch.WordTrace tailWord_4715976 prefixEnd_4715976 2421562443067945955911627 := by
  unfold tailWord_4715976
  simp only [CollatzResearch.WordTrace]
  refine ⟨86002887781415925711391891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114670517041887900948522521 86002887781415925711391891)
  ·
    refine ⟨129004331672123888567087837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86002887781415925711391891 129004331672123888567087837)
    ·
      refine ⟨48376624377046458212657939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129004331672123888567087837 48376624377046458212657939)
      ·
        refine ⟨72564936565569687318986909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48376624377046458212657939 72564936565569687318986909)
        ·
          refine ⟨27211851212088632744620091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72564936565569687318986909 27211851212088632744620091)
          ·
            refine ⟨40817776818132949116930137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27211851212088632744620091 40817776818132949116930137)
            ·
              refine ⟨30613332613599711837697603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40817776818132949116930137 30613332613599711837697603)
              ·
                refine ⟨45919998920399567756546405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30613332613599711837697603 45919998920399567756546405)
                ·
                  refine ⟨8609999797574918954352451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45919998920399567756546405 8609999797574918954352451)
                  ·
                    refine ⟨12914999696362378431528677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8609999797574918954352451 12914999696362378431528677)
                    ·
                      refine ⟨2421562443067945955911627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12914999696362378431528677 2421562443067945955911627)
                      ·
                        rfl

theorem cell23_4715976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_4715976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715976 prefixEnd_4715976 := by exact prefixLift 4715976
  have htrace : WordTrace (prefixWord ++ tailWord_4715976) baseStart_4715976 baseEnd_4715976 := by
    simpa [prefixWord, tailWord_4715976, baseEnd_4715976] using wordTrace_append hprefix tailTrace_4715976
  have hstable : (prefixWord ++ tailWord_4715976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715976).length < 2 ^ (prefixWord ++ tailWord_4715976).sum := by decide
  have hdescent : baseEnd_4715976 < baseStart_4715976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715979 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5]
def baseStart_4715979 : Nat := 118140960795 + 4715979 * 2 ^ 59
def prefixEnd_4715979 : Nat := 4983230072969 + 3 ^ 40 * 4715979 * 2
def baseEnd_4715979 : Nat := 2421563983509909444174113

theorem tailTrace_4715979 : CollatzResearch.WordTrace tailWord_4715979 prefixEnd_4715979 2421563983509909444174113 := by
  unfold tailWord_4715979
  simp only [CollatzResearch.WordTrace]
  refine ⟨172005884981820982935142991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114670589987880655290095327 172005884981820982935142991)
  ·
    refine ⟨258008827472731474402714487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172005884981820982935142991 258008827472731474402714487)
    ·
      refine ⟨387013241209097211604071731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258008827472731474402714487 387013241209097211604071731)
      ·
        refine ⟨580519861813645817406107597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387013241209097211604071731 580519861813645817406107597)
        ·
          refine ⟨217694948180117181527290349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 580519861813645817406107597 217694948180117181527290349)
          ·
            refine ⟨81635605567543943072733881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217694948180117181527290349 81635605567543943072733881)
            ·
              refine ⟨61226704175657957304550411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81635605567543943072733881 61226704175657957304550411)
              ·
                refine ⟨91840056263486935956825617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61226704175657957304550411 91840056263486935956825617)
                ·
                  refine ⟨68880042197615201967619213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91840056263486935956825617 68880042197615201967619213)
                  ·
                    refine ⟨25830015824105700737857205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68880042197615201967619213 25830015824105700737857205)
                    ·
                      refine ⟨2421563983509909444174113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25830015824105700737857205 2421563983509909444174113)
                      ·
                        rfl

theorem cell23_4715979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_4715979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715979 prefixEnd_4715979 := by exact prefixLift 4715979
  have htrace : WordTrace (prefixWord ++ tailWord_4715979) baseStart_4715979 baseEnd_4715979 := by
    simpa [prefixWord, tailWord_4715979, baseEnd_4715979] using wordTrace_append hprefix tailTrace_4715979
  have hstable : (prefixWord ++ tailWord_4715979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715979).length < 2 ^ (prefixWord ++ tailWord_4715979).sum := by decide
  have hdescent : baseEnd_4715979 < baseStart_4715979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4715993 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 2, 4, 2]
def baseStart_4715993 : Nat := 118140960795 + 4715993 * 2 ^ 59
def prefixEnd_4715993 : Nat := 4983230072969 + 3 ^ 40 * 4715993 * 2
def baseEnd_4715993 : Nat := 2421571172239072389399049

theorem tailTrace_4715993 : CollatzResearch.WordTrace tailWord_4715993 prefixEnd_4715993 2421571172239072389399049 := by
  unfold tailWord_4715993
  simp only [CollatzResearch.WordTrace]
  refine ⟨172006395603770263326152633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114670930402513508884101755 172006395603770263326152633)
  ·
    refine ⟨129004796702827697494614475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172006395603770263326152633 129004796702827697494614475)
    ·
      refine ⟨193507195054241546241921713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129004796702827697494614475 193507195054241546241921713)
      ·
        refine ⟨145130396290681159681441285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193507195054241546241921713 145130396290681159681441285)
        ·
          refine ⟨27211949304502717440270241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145130396290681159681441285 27211949304502717440270241)
          ·
            refine ⟨20408961978377038080202681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27211949304502717440270241 20408961978377038080202681)
            ·
              refine ⟨15306721483782778560152011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20408961978377038080202681 15306721483782778560152011)
              ·
                refine ⟨22960082225674167840228017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15306721483782778560152011 22960082225674167840228017)
                ·
                  refine ⟨17220061669255625880171013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22960082225674167840228017 17220061669255625880171013)
                  ·
                    refine ⟨3228761562985429852532065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17220061669255625880171013 3228761562985429852532065)
                    ·
                      refine ⟨2421571172239072389399049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228761562985429852532065 2421571172239072389399049)
                      ·
                        rfl

theorem cell23_4715993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_4715993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4715993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4715993 prefixEnd_4715993 := by exact prefixLift 4715993
  have htrace : WordTrace (prefixWord ++ tailWord_4715993) baseStart_4715993 baseEnd_4715993 := by
    simpa [prefixWord, tailWord_4715993, baseEnd_4715993] using wordTrace_append hprefix tailTrace_4715993
  have hstable : (prefixWord ++ tailWord_4715993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4715993).length < 2 ^ (prefixWord ++ tailWord_4715993).sum := by decide
  have hdescent : baseEnd_4715993 < baseStart_4715993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4715993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716003 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 3, 4]
def baseStart_4716003 : Nat := 118140960795 + 4716003 * 2 ^ 59
def prefixEnd_4716003 : Nat := 4983230072969 + 3 ^ 40 * 4716003 * 2
def baseEnd_4716003 : Nat := 807192102348539116758001

theorem tailTrace_4716003 : CollatzResearch.WordTrace tailWord_4716003 prefixEnd_4716003 807192102348539116758001 := by
  unfold tailWord_4716003
  simp only [CollatzResearch.WordTrace]
  refine ⟨172006760333734035034016663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114671173555822690022677775 172006760333734035034016663)
  ·
    refine ⟨258010140500601052551024995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172006760333734035034016663 258010140500601052551024995)
    ·
      refine ⟨387015210750901578826537493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258010140500601052551024995 387015210750901578826537493)
      ·
        refine ⟨18141338003948511507493945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 387015210750901578826537493 18141338003948511507493945)
        ·
          refine ⟨13606003502961383630620459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18141338003948511507493945 13606003502961383630620459)
          ·
            refine ⟨20409005254442075445930689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13606003502961383630620459 20409005254442075445930689)
            ·
              refine ⟨15306753940831556584448017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20409005254442075445930689 15306753940831556584448017)
              ·
                refine ⟨11480065455623667438336013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15306753940831556584448017 11480065455623667438336013)
                ·
                  refine ⟨4305024545858875289376005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11480065455623667438336013 4305024545858875289376005)
                  ·
                    refine ⟨807192102348539116758001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305024545858875289376005 807192102348539116758001)
                    ·
                      rfl

theorem cell23_4716003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 4].length) (baseStart_4716003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716003 prefixEnd_4716003 := by exact prefixLift 4716003
  have htrace : WordTrace (prefixWord ++ tailWord_4716003) baseStart_4716003 baseEnd_4716003 := by
    simpa [prefixWord, tailWord_4716003, baseEnd_4716003] using wordTrace_append hprefix tailTrace_4716003
  have hstable : (prefixWord ++ tailWord_4716003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716003).length < 2 ^ (prefixWord ++ tailWord_4716003).sum := by decide
  have hdescent : baseEnd_4716003 < baseStart_4716003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716019 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8]
def baseStart_4716019 : Nat := 118140960795 + 4716019 * 2 ^ 59
def prefixEnd_4716019 : Nat := 4983230072969 + 3 ^ 40 * 4716019 * 2
def baseEnd_4716019 : Nat := 2421584522736089287673929

theorem tailTrace_4716019 : CollatzResearch.WordTrace tailWord_4716019 prefixEnd_4716019 2421584522736089287673929 := by
  unfold tailWord_4716019
  simp only [CollatzResearch.WordTrace]
  refine ⟨172007343901676069766599111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114671562601117379844399407 172007343901676069766599111)
  ·
    refine ⟨258011015852514104649898667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172007343901676069766599111 258011015852514104649898667)
    ·
      refine ⟨387016523778771156974848001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258011015852514104649898667 387016523778771156974848001)
      ·
        refine ⟨290262392834078367731136001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387016523778771156974848001 290262392834078367731136001)
        ·
          refine ⟨217696794625558775798352001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290262392834078367731136001 217696794625558775798352001)
          ·
            refine ⟨163272595969169081848764001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217696794625558775798352001 163272595969169081848764001)
            ·
              refine ⟨122454446976876811386573001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163272595969169081848764001 122454446976876811386573001)
              ·
                refine ⟨91840835232657608539929751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122454446976876811386573001 91840835232657608539929751)
                ·
                  refine ⟨137761252848986412809894627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91840835232657608539929751 137761252848986412809894627)
                  ·
                    refine ⟨206641879273479619214841941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137761252848986412809894627 206641879273479619214841941)
                    ·
                      refine ⟨2421584522736089287673929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 206641879273479619214841941 2421584522736089287673929)
                      ·
                        rfl

theorem cell23_4716019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_4716019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716019 prefixEnd_4716019 := by exact prefixLift 4716019
  have htrace : WordTrace (prefixWord ++ tailWord_4716019) baseStart_4716019 baseEnd_4716019 := by
    simpa [prefixWord, tailWord_4716019, baseEnd_4716019] using wordTrace_append hprefix tailTrace_4716019
  have hstable : (prefixWord ++ tailWord_4716019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716019).length < 2 ^ (prefixWord ++ tailWord_4716019).sum := by decide
  have hdescent : baseEnd_4716019 < baseStart_4716019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716063 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 1, 5]
def baseStart_4716063 : Nat := 118140960795 + 4716063 * 2 ^ 59
def prefixEnd_4716063 : Nat := 4983230072969 + 3 ^ 40 * 4716063 * 2
def baseEnd_4716063 : Nat := 807202371961629038507909

theorem tailTrace_4716063 : CollatzResearch.WordTrace tailWord_4716063 prefixEnd_4716063 807202371961629038507909 := by
  unfold tailWord_4716063
  simp only [CollatzResearch.WordTrace]
  refine ⟨172008948713516665281200843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114672632475677776854133895 172008948713516665281200843)
  ·
    refine ⟨258013423070274997921801265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172008948713516665281200843 258013423070274997921801265)
    ·
      refine ⟨193510067302706248441350949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258013423070274997921801265 193510067302706248441350949)
      ·
        refine ⟨36283137619257421582753303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193510067302706248441350949 36283137619257421582753303)
        ·
          refine ⟨54424706428886132374129955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36283137619257421582753303 54424706428886132374129955)
          ·
            refine ⟨81637059643329198561194933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54424706428886132374129955 81637059643329198561194933)
            ·
              refine ⟨7653474341562112365112025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81637059643329198561194933 7653474341562112365112025)
              ·
                refine ⟨5740105756171584273834019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7653474341562112365112025 5740105756171584273834019)
                ·
                  refine ⟨8610158634257376410751029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5740105756171584273834019 8610158634257376410751029)
                  ·
                    refine ⟨807202371961629038507909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8610158634257376410751029 807202371961629038507909)
                    ·
                      rfl

theorem cell23_4716063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_4716063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716063 prefixEnd_4716063 := by exact prefixLift 4716063
  have htrace : WordTrace (prefixWord ++ tailWord_4716063) baseStart_4716063 baseEnd_4716063 := by
    simpa [prefixWord, tailWord_4716063, baseEnd_4716063] using wordTrace_append hprefix tailTrace_4716063
  have hstable : (prefixWord ++ tailWord_4716063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716063).length < 2 ^ (prefixWord ++ tailWord_4716063).sum := by decide
  have hdescent : baseEnd_4716063 < baseStart_4716063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716096 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_4716096 : Nat := 118140960795 + 4716096 * 2 ^ 59
def prefixEnd_4716096 : Nat := 4983230072969 + 3 ^ 40 * 4716096 * 2
def baseEnd_4716096 : Nat := 2421624060746485486411075

theorem tailTrace_4716096 : CollatzResearch.WordTrace tailWord_4716096 prefixEnd_4716096 2421624060746485486411075 := by
  unfold tailWord_4716096
  simp only [CollatzResearch.WordTrace]
  refine ⟨86005076161198555958576071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114673434881598074611434761 86005076161198555958576071)
  ·
    refine ⟨129007614241797833937864107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86005076161198555958576071 129007614241797833937864107)
    ·
      refine ⟨193511421362696750906796161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129007614241797833937864107 193511421362696750906796161)
      ·
        refine ⟨145133566022022563180097121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193511421362696750906796161 145133566022022563180097121)
        ·
          refine ⟨108850174516516922385072841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145133566022022563180097121 108850174516516922385072841)
          ·
            refine ⟨81637630887387691788804631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108850174516516922385072841 81637630887387691788804631)
            ·
              refine ⟨122456446331081537683206947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81637630887387691788804631 122456446331081537683206947)
              ·
                refine ⟨183684669496622306524810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122456446331081537683206947 183684669496622306524810421)
                ·
                  refine ⟨17220437765308341236700977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183684669496622306524810421 17220437765308341236700977)
                  ·
                    refine ⟨12915328323981255927525733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17220437765308341236700977 12915328323981255927525733)
                    ·
                      refine ⟨2421624060746485486411075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12915328323981255927525733 2421624060746485486411075)
                      ·
                        rfl

theorem cell23_4716096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_4716096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716096 prefixEnd_4716096 := by exact prefixLift 4716096
  have htrace : WordTrace (prefixWord ++ tailWord_4716096) baseStart_4716096 baseEnd_4716096 := by
    simpa [prefixWord, tailWord_4716096, baseEnd_4716096] using wordTrace_append hprefix tailTrace_4716096
  have hstable : (prefixWord ++ tailWord_4716096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716096).length < 2 ^ (prefixWord ++ tailWord_4716096).sum := by decide
  have hdescent : baseEnd_4716096 < baseStart_4716096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716113 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_4716113 : Nat := 118140960795 + 4716113 * 2 ^ 59
def prefixEnd_4716113 : Nat := 4983230072969 + 3 ^ 40 * 4716113 * 2
def baseEnd_4716113 : Nat := 2421632789917611919898497

theorem tailTrace_4716113 : CollatzResearch.WordTrace tailWord_4716113 prefixEnd_4716113 2421632789917611919898497 := by
  unfold tailWord_4716113
  simp only [CollatzResearch.WordTrace]
  refine ⟨172010772363335523820520993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114673848242223682547013995 172010772363335523820520993)
  ·
    refine ⟨129008079272501642865390745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172010772363335523820520993 129008079272501642865390745)
    ·
      refine ⟨96756059454376232149043059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129008079272501642865390745 96756059454376232149043059)
      ·
        refine ⟨145134089181564348223564589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96756059454376232149043059 145134089181564348223564589)
        ·
          refine ⟨54425283443086630583836721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145134089181564348223564589 54425283443086630583836721)
          ·
            refine ⟨40818962582314972937877541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54425283443086630583836721 40818962582314972937877541)
            ·
              refine ⟨7653555484184057425852039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40818962582314972937877541 7653555484184057425852039)
              ·
                refine ⟨11480333226276086138778059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7653555484184057425852039 11480333226276086138778059)
                ·
                  refine ⟨17220499839414129208167089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11480333226276086138778059 17220499839414129208167089)
                  ·
                    refine ⟨12915374879560596906125317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17220499839414129208167089 12915374879560596906125317)
                    ·
                      refine ⟨2421632789917611919898497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12915374879560596906125317 2421632789917611919898497)
                      ·
                        rfl

theorem cell23_4716113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_4716113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716113 prefixEnd_4716113 := by exact prefixLift 4716113
  have htrace : WordTrace (prefixWord ++ tailWord_4716113) baseStart_4716113 baseEnd_4716113 := by
    simpa [prefixWord, tailWord_4716113, baseEnd_4716113] using wordTrace_append hprefix tailTrace_4716113
  have hstable : (prefixWord ++ tailWord_4716113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716113).length < 2 ^ (prefixWord ++ tailWord_4716113).sum := by decide
  have hdescent : baseEnd_4716113 < baseStart_4716113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716176 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_4716176 : Nat := 118140960795 + 4716176 * 2 ^ 59
def prefixEnd_4716176 : Nat := 4983230072969 + 3 ^ 40 * 4716176 * 2
def baseEnd_4716176 : Nat := 2421665139198845173410707

theorem tailTrace_4716176 : CollatzResearch.WordTrace tailWord_4716176 prefixEnd_4716176 2421665139198845173410707 := by
  unfold tailWord_4716176
  simp only [CollatzResearch.WordTrace]
  refine ⟨86006535081053642790032191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114675380108071523720042921 86006535081053642790032191)
  ·
    refine ⟨129009802621580464185048287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86006535081053642790032191 129009802621580464185048287)
    ·
      refine ⟨193514703932370696277572431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129009802621580464185048287 193514703932370696277572431)
      ·
        refine ⟨290272055898556044416358647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193514703932370696277572431 290272055898556044416358647)
        ·
          refine ⟨435408083847834066624537971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290272055898556044416358647 435408083847834066624537971)
          ·
            refine ⟨653112125771751099936806957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435408083847834066624537971 653112125771751099936806957)
            ·
              refine ⟨244917047164406662476302609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653112125771751099936806957 244917047164406662476302609)
              ·
                refine ⟨183687785373304996857226957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244917047164406662476302609 183687785373304996857226957)
                ·
                  refine ⟨68882919514989373821460109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183687785373304996857226957 68882919514989373821460109)
                  ·
                    refine ⟨25831094818121015183047541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68882919514989373821460109 25831094818121015183047541)
                    ·
                      refine ⟨2421665139198845173410707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25831094818121015183047541 2421665139198845173410707)
                      ·
                        rfl

theorem cell23_4716176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_4716176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716176 prefixEnd_4716176 := by exact prefixLift 4716176
  have htrace : WordTrace (prefixWord ++ tailWord_4716176) baseStart_4716176 baseEnd_4716176 := by
    simpa [prefixWord, tailWord_4716176, baseEnd_4716176] using wordTrace_append hprefix tailTrace_4716176
  have hstable : (prefixWord ++ tailWord_4716176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716176).length < 2 ^ (prefixWord ++ tailWord_4716176).sum := by decide
  have hdescent : baseEnd_4716176 < baseStart_4716176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716193 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4716193 : Nat := 118140960795 + 4716193 * 2 ^ 59
def prefixEnd_4716193 : Nat := 4983230072969 + 3 ^ 40 * 4716193 * 2
def baseEnd_4716193 : Nat := 2421673868369971606898129

theorem tailTrace_4716193 : CollatzResearch.WordTrace tailWord_4716193 prefixEnd_4716193 2421673868369971606898129 := by
  unfold tailWord_4716193
  simp only [CollatzResearch.WordTrace]
  refine ⟨172013690203045697483433233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114675793468697131655622155 172013690203045697483433233)
  ·
    refine ⟨129010267652284273112574925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172013690203045697483433233 129010267652284273112574925)
    ·
      refine ⟨48378850369606602417215597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129010267652284273112574925 48378850369606602417215597)
      ·
        refine ⟨18142068888602475906455849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48378850369606602417215597 18142068888602475906455849)
        ·
          refine ⟨13606551666451856929841887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18142068888602475906455849 13606551666451856929841887)
          ·
            refine ⟨20409827499677785394762831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13606551666451856929841887 20409827499677785394762831)
            ·
              refine ⟨30614741249516678092144247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20409827499677785394762831 30614741249516678092144247)
              ·
                refine ⟨45922111874275017138216371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30614741249516678092144247 45922111874275017138216371)
                ·
                  refine ⟨68883167811412525707324557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45922111874275017138216371 68883167811412525707324557)
                  ·
                    refine ⟨25831187929279697140246709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68883167811412525707324557 25831187929279697140246709)
                    ·
                      refine ⟨2421673868369971606898129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25831187929279697140246709 2421673868369971606898129)
                      ·
                        rfl

theorem cell23_4716193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4716193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716193 prefixEnd_4716193 := by exact prefixLift 4716193
  have htrace : WordTrace (prefixWord ++ tailWord_4716193) baseStart_4716193 baseEnd_4716193 := by
    simpa [prefixWord, tailWord_4716193, baseEnd_4716193] using wordTrace_append hprefix tailTrace_4716193
  have hstable : (prefixWord ++ tailWord_4716193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716193).length < 2 ^ (prefixWord ++ tailWord_4716193).sum := by decide
  have hdescent : baseEnd_4716193 < baseStart_4716193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716207 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 2, 2, 2]
def baseStart_4716207 : Nat := 118140960795 + 4716207 * 2 ^ 59
def prefixEnd_4716207 : Nat := 4983230072969 + 3 ^ 40 * 4716207 * 2
def baseEnd_4716207 : Nat := 2421681057099134552123065

theorem tailTrace_4716207 : CollatzResearch.WordTrace tailWord_4716207 prefixEnd_4716207 2421681057099134552123065 := by
  unfold tailWord_4716207
  simp only [CollatzResearch.WordTrace]
  refine ⟨172014200824994977874442875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114676133883329985249628583 172014200824994977874442875)
  ·
    refine ⟨258021301237492466811664313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172014200824994977874442875 258021301237492466811664313)
    ·
      refine ⟨193515975928119350108748235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258021301237492466811664313 193515975928119350108748235)
      ·
        refine ⟨290273963892179025163122353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193515975928119350108748235 290273963892179025163122353)
        ·
          refine ⟨217705472919134268872341765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290273963892179025163122353 217705472919134268872341765)
          ·
            refine ⟨40819776172337675413564081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217705472919134268872341765 40819776172337675413564081)
            ·
              refine ⟨30614832129253256560173061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40819776172337675413564081 30614832129253256560173061)
              ·
                refine ⟨5740281024234985605032449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30614832129253256560173061 5740281024234985605032449)
                ·
                  refine ⟨4305210768176239203774337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5740281024234985605032449 4305210768176239203774337)
                  ·
                    refine ⟨3228908076132179402830753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4305210768176239203774337 3228908076132179402830753)
                    ·
                      refine ⟨2421681057099134552123065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3228908076132179402830753 2421681057099134552123065)
                      ·
                        rfl

theorem cell23_4716207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 2, 2].length) (baseStart_4716207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716207 prefixEnd_4716207 := by exact prefixLift 4716207
  have htrace : WordTrace (prefixWord ++ tailWord_4716207) baseStart_4716207 baseEnd_4716207 := by
    simpa [prefixWord, tailWord_4716207, baseEnd_4716207] using wordTrace_append hprefix tailTrace_4716207
  have hstable : (prefixWord ++ tailWord_4716207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716207).length < 2 ^ (prefixWord ++ tailWord_4716207).sum := by decide
  have hdescent : baseEnd_4716207 < baseStart_4716207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716223 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 3]
def baseStart_4716223 : Nat := 118140960795 + 4716223 * 2 ^ 59
def prefixEnd_4716223 : Nat := 4983230072969 + 3 ^ 40 * 4716223 * 2
def baseEnd_4716223 : Nat := 2421689272789606489522991

theorem tailTrace_4716223 : CollatzResearch.WordTrace tailWord_4716223 prefixEnd_4716223 2421689272789606489522991 := by
  unfold tailWord_4716223
  simp only [CollatzResearch.WordTrace]
  refine ⟨172014784392937012607025323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114676522928624675071350215 172014784392937012607025323)
  ·
    refine ⟨258022176589405518910537985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172014784392937012607025323 258022176589405518910537985)
    ·
      refine ⟨193516632442054139182903489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258022176589405518910537985 193516632442054139182903489)
      ·
        refine ⟨145137474331540604387177617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193516632442054139182903489 145137474331540604387177617)
        ·
          refine ⟨108853105748655453290383213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145137474331540604387177617 108853105748655453290383213)
          ·
            refine ⟨40819914655745794983893705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108853105748655453290383213 40819914655745794983893705)
            ·
              refine ⟨30614935991809346237920279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40819914655745794983893705 30614935991809346237920279)
              ·
                refine ⟨45922403987714019356880419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30614935991809346237920279 45922403987714019356880419)
                ·
                  refine ⟨68883605981571029035320629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45922403987714019356880419 68883605981571029035320629)
                  ·
                    refine ⟨6457838060772283972061309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68883605981571029035320629 6457838060772283972061309)
                    ·
                      refine ⟨2421689272789606489522991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6457838060772283972061309 2421689272789606489522991)
                      ·
                        rfl

theorem cell23_4716223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_4716223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716223 prefixEnd_4716223 := by exact prefixLift 4716223
  have htrace : WordTrace (prefixWord ++ tailWord_4716223) baseStart_4716223 baseEnd_4716223 := by
    simpa [prefixWord, tailWord_4716223, baseEnd_4716223] using wordTrace_append hprefix tailTrace_4716223
  have hstable : (prefixWord ++ tailWord_4716223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716223).length < 2 ^ (prefixWord ++ tailWord_4716223).sum := by decide
  have hdescent : baseEnd_4716223 < baseStart_4716223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716264 : List Nat := [2, 1, 4, 1, 3, 3, 2, 2, 5]
def baseStart_4716264 : Nat := 118140960795 + 4716264 * 2 ^ 59
def prefixEnd_4716264 : Nat := 4983230072969 + 3 ^ 40 * 4716264 * 2
def baseEnd_4716264 : Nat := 269078925055160092123367

theorem tailTrace_4716264 : CollatzResearch.WordTrace tailWord_4716264 prefixEnd_4716264 269078925055160092123367 := by
  unfold tailWord_4716264
  simp only [CollatzResearch.WordTrace]
  refine ⟨86008139892894238304633923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114677519857192317739511897 86008139892894238304633923)
  ·
    refine ⟨129012209839341357456950885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86008139892894238304633923 129012209839341357456950885)
    ·
      refine ⟨24189789344876504523178291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129012209839341357456950885 24189789344876504523178291)
      ·
        refine ⟨36284684017314756784767437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24189789344876504523178291 36284684017314756784767437)
        ·
          refine ⟨13606756506493033794287789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36284684017314756784767437 13606756506493033794287789)
          ·
            refine ⟨5102533689934887672857921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13606756506493033794287789 5102533689934887672857921)
            ·
              refine ⟨3826900267451165754643441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5102533689934887672857921 3826900267451165754643441)
              ·
                refine ⟨2870175200588374315982581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826900267451165754643441 2870175200588374315982581)
                ·
                  refine ⟨269078925055160092123367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2870175200588374315982581 269078925055160092123367)
                  ·
                    rfl

theorem cell23_4716264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 5].length) (baseStart_4716264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716264 prefixEnd_4716264 := by exact prefixLift 4716264
  have htrace : WordTrace (prefixWord ++ tailWord_4716264) baseStart_4716264 baseEnd_4716264 := by
    simpa [prefixWord, tailWord_4716264, baseEnd_4716264] using wordTrace_append hprefix tailTrace_4716264
  have hstable : (prefixWord ++ tailWord_4716264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716264).length < 2 ^ (prefixWord ++ tailWord_4716264).sum := by decide
  have hdescent : baseEnd_4716264 < baseStart_4716264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716323 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4716323 : Nat := 118140960795 + 4716323 * 2 ^ 59
def prefixEnd_4716323 : Nat := 4983230072969 + 3 ^ 40 * 4716323 * 2
def baseEnd_4716323 : Nat := 2421740620855056098272531

theorem tailTrace_4716323 : CollatzResearch.WordTrace tailWord_4716323 prefixEnd_4716323 2421740620855056098272531 := by
  unfold tailWord_4716323
  simp only [CollatzResearch.WordTrace]
  refine ⟨172018431692574729685665623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114678954461716486457110415 172018431692574729685665623)
  ·
    refine ⟨258027647538862094528498435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172018431692574729685665623 258027647538862094528498435)
    ·
      refine ⟨387041471308293141792747653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258027647538862094528498435 387041471308293141792747653)
      ·
        refine ⟨72570275870304964086140185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387041471308293141792747653 72570275870304964086140185)
        ·
          refine ⟨54427706902728723064605139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72570275870304964086140185 54427706902728723064605139)
          ·
            refine ⟨81641560354093084596907709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54427706902728723064605139 81641560354093084596907709)
            ·
              refine ⟨30615585132784906723840391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81641560354093084596907709 30615585132784906723840391)
              ·
                refine ⟨45923377699177360085760587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30615585132784906723840391 45923377699177360085760587)
                ·
                  refine ⟨68885066548766040128640881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45923377699177360085760587 68885066548766040128640881)
                  ·
                    refine ⟨51663799911574530096480661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68885066548766040128640881 51663799911574530096480661)
                    ·
                      refine ⟨2421740620855056098272531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51663799911574530096480661 2421740620855056098272531)
                      ·
                        rfl

theorem cell23_4716323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4716323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716323 prefixEnd_4716323 := by exact prefixLift 4716323
  have htrace : WordTrace (prefixWord ++ tailWord_4716323) baseStart_4716323 baseEnd_4716323 := by
    simpa [prefixWord, tailWord_4716323, baseEnd_4716323] using wordTrace_append hprefix tailTrace_4716323
  have hstable : (prefixWord ++ tailWord_4716323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716323).length < 2 ^ (prefixWord ++ tailWord_4716323).sum := by decide
  have hdescent : baseEnd_4716323 < baseStart_4716323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716324 : List Nat := [2, 3, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_4716324 : Nat := 118140960795 + 4716324 * 2 ^ 59
def prefixEnd_4716324 : Nat := 4983230072969 + 3 ^ 40 * 4716324 * 2
def baseEnd_4716324 : Nat := 807247044778570198120009

theorem tailTrace_4716324 : CollatzResearch.WordTrace tailWord_4716324 prefixEnd_4716324 807247044778570198120009 := by
  unfold tailWord_4716324
  simp only [CollatzResearch.WordTrace]
  refine ⟨86009234082785553428226013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114678978777047404570968017 86009234082785553428226013)
  ·
    refine ⟨32253462781044582535584755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86009234082785553428226013 32253462781044582535584755)
    ·
      refine ⟨48380194171566873803377133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32253462781044582535584755 48380194171566873803377133)
      ·
        refine ⟨18142572814337577676266425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48380194171566873803377133 18142572814337577676266425)
        ·
          refine ⟨13606929610753183257199819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18142572814337577676266425 13606929610753183257199819)
          ·
            refine ⟨20410394416129774885799729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13606929610753183257199819 20410394416129774885799729)
            ·
              refine ⟨15307795812097331164349797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20410394416129774885799729 15307795812097331164349797)
              ·
                refine ⟨2870211714768249593315587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15307795812097331164349797 2870211714768249593315587)
                ·
                  refine ⟨4305317572152374389973381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870211714768249593315587 4305317572152374389973381)
                  ·
                    refine ⟨807247044778570198120009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305317572152374389973381 807247044778570198120009)
                    ·
                      rfl

theorem cell23_4716324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_4716324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716324 prefixEnd_4716324 := by exact prefixLift 4716324
  have htrace : WordTrace (prefixWord ++ tailWord_4716324) baseStart_4716324 baseEnd_4716324 := by
    simpa [prefixWord, tailWord_4716324, baseEnd_4716324] using wordTrace_append hprefix tailTrace_4716324
  have hstable : (prefixWord ++ tailWord_4716324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716324).length < 2 ^ (prefixWord ++ tailWord_4716324).sum := by decide
  have hdescent : baseEnd_4716324 < baseStart_4716324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716337 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 6]
def baseStart_4716337 : Nat := 118140960795 + 4716337 * 2 ^ 59
def prefixEnd_4716337 : Nat := 4983230072969 + 3 ^ 40 * 4716337 * 2
def baseEnd_4716337 : Nat := 269083089953802115944163

theorem tailTrace_4716337 : CollatzResearch.WordTrace tailWord_4716337 prefixEnd_4716337 269083089953802115944163 := by
  unfold tailWord_4716337
  simp only [CollatzResearch.WordTrace]
  refine ⟨172018942314524010076675265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114679294876349340051116843 172018942314524010076675265)
  ·
    refine ⟨129014206735893007557506449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172018942314524010076675265 129014206735893007557506449)
    ·
      refine ⟨96760655051919755668129837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129014206735893007557506449 96760655051919755668129837)
      ·
        refine ⟨36285245644469908375548689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96760655051919755668129837 36285245644469908375548689)
        ·
          refine ⟨27213934233352431281661517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36285245644469908375548689 27213934233352431281661517)
          ·
            refine ⟨10205225337507161730623069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27213934233352431281661517 10205225337507161730623069)
            ·
              refine ⟨3826959501565185648983651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10205225337507161730623069 3826959501565185648983651)
              ·
                refine ⟨5740439252347778473475477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3826959501565185648983651 5740439252347778473475477)
                ·
                  refine ⟨269083089953802115944163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5740439252347778473475477 269083089953802115944163)
                  ·
                    rfl

theorem cell23_4716337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 6].length) (baseStart_4716337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716337 prefixEnd_4716337 := by exact prefixLift 4716337
  have htrace : WordTrace (prefixWord ++ tailWord_4716337) baseStart_4716337 baseEnd_4716337 := by
    simpa [prefixWord, tailWord_4716337, baseEnd_4716337] using wordTrace_append hprefix tailTrace_4716337
  have hstable : (prefixWord ++ tailWord_4716337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716337).length < 2 ^ (prefixWord ++ tailWord_4716337).sum := by decide
  have hdescent : baseEnd_4716337 < baseStart_4716337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716357 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 2, 3, 2]
def baseStart_4716357 : Nat := 118140960795 + 4716357 * 2 ^ 59
def prefixEnd_4716357 : Nat := 4983230072969 + 3 ^ 40 * 4716357 * 2
def baseEnd_4716357 : Nat := 2421758079197308965247375

theorem tailTrace_4716357 : CollatzResearch.WordTrace tailWord_4716357 prefixEnd_4716357 2421758079197308965247375 := by
  unfold tailWord_4716357
  simp only [CollatzResearch.WordTrace]
  refine ⟨172019671774451553492403325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114679781182967702328268883 172019671774451553492403325)
  ·
    refine ⟨64507376915419332559651247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172019671774451553492403325 64507376915419332559651247)
    ·
      refine ⟨96761065373128998839476871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64507376915419332559651247 96761065373128998839476871)
      ·
        refine ⟨145141598059693498259215307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96761065373128998839476871 145141598059693498259215307)
        ·
          refine ⟨217712397089540247388822961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145141598059693498259215307 217712397089540247388822961)
          ·
            refine ⟨163284297817155185541617221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217712397089540247388822961 163284297817155185541617221)
            ·
              refine ⟨30615805840716597289053229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163284297817155185541617221 30615805840716597289053229)
              ·
                refine ⟨11480927190268723983394961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30615805840716597289053229 11480927190268723983394961)
                ·
                  refine ⟨8610695392701542987546221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11480927190268723983394961 8610695392701542987546221)
                  ·
                    refine ⟨3229010772263078620329833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8610695392701542987546221 3229010772263078620329833)
                    ·
                      refine ⟨2421758079197308965247375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229010772263078620329833 2421758079197308965247375)
                      ·
                        rfl

theorem cell23_4716357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_4716357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716357 prefixEnd_4716357 := by exact prefixLift 4716357
  have htrace : WordTrace (prefixWord ++ tailWord_4716357) baseStart_4716357 baseEnd_4716357 := by
    simpa [prefixWord, tailWord_4716357, baseEnd_4716357] using wordTrace_append hprefix tailTrace_4716357
  have hstable : (prefixWord ++ tailWord_4716357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716357).length < 2 ^ (prefixWord ++ tailWord_4716357).sum := by decide
  have hdescent : baseEnd_4716357 < baseStart_4716357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716358 : List Nat := [6, 1, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4716358 : Nat := 118140960795 + 4716358 * 2 ^ 59
def prefixEnd_4716358 : Nat := 4983230072969 + 3 ^ 40 * 4716358 * 2
def baseEnd_4716358 : Nat := 807252864225987820444957

theorem tailTrace_4716358 : CollatzResearch.WordTrace tailWord_4716358 prefixEnd_4716358 807252864225987820444957 := by
  unfold tailWord_4716358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5375615882732747833224679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114679805498298620442126485 5375615882732747833224679)
  ·
    refine ⟨8063423824099121749837019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5375615882732747833224679 8063423824099121749837019)
    ·
      refine ⟨12095135736148682624755529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8063423824099121749837019 12095135736148682624755529)
      ·
        refine ⟨9071351802111511968566647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12095135736148682624755529 9071351802111511968566647)
        ·
          refine ⟨13607027703167267952849971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9071351802111511968566647 13607027703167267952849971)
          ·
            refine ⟨20410541554750901929274957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13607027703167267952849971 20410541554750901929274957)
            ·
              refine ⟨7653953083031588223478109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20410541554750901929274957 7653953083031588223478109)
              ·
                refine ⟨2870232406136845583804291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7653953083031588223478109 2870232406136845583804291)
                ·
                  refine ⟨4305348609205268375706437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870232406136845583804291 4305348609205268375706437)
                  ·
                    refine ⟨807252864225987820444957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305348609205268375706437 807252864225987820444957)
                    ·
                      rfl

theorem cell23_4716358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4716358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716358 prefixEnd_4716358 := by exact prefixLift 4716358
  have htrace : WordTrace (prefixWord ++ tailWord_4716358) baseStart_4716358 baseEnd_4716358 := by
    simpa [prefixWord, tailWord_4716358, baseEnd_4716358] using wordTrace_append hprefix tailTrace_4716358
  have hstable : (prefixWord ++ tailWord_4716358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716358).length < 2 ^ (prefixWord ++ tailWord_4716358).sum := by decide
  have hdescent : baseEnd_4716358 < baseStart_4716358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716400 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_4716400 : Nat := 118140960795 + 4716400 * 2 ^ 59
def prefixEnd_4716400 : Nat := 4983230072969 + 3 ^ 40 * 4716400 * 2
def baseEnd_4716400 : Nat := 2421780158865452297009677

theorem tailTrace_4716400 : CollatzResearch.WordTrace tailWord_4716400 prefixEnd_4716400 2421780158865452297009677 := by
  unfold tailWord_4716400
  simp only [CollatzResearch.WordTrace]
  refine ⟨86010620056647885918109327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114680826742197181224145769 86010620056647885918109327)
  ·
    refine ⟨129015930084971828877163991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86010620056647885918109327 129015930084971828877163991)
    ·
      refine ⟨193523895127457743315745987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129015930084971828877163991 193523895127457743315745987)
      ·
        refine ⟨290285842691186614973618981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193523895127457743315745987 290285842691186614973618981)
        ·
          refine ⟨54428595504597490307553559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290285842691186614973618981 54428595504597490307553559)
          ·
            refine ⟨81642893256896235461330339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54428595504597490307553559 81642893256896235461330339)
            ·
              refine ⟨122464339885344353191995509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81642893256896235461330339 122464339885344353191995509)
              ·
                refine ⟨11481031864251033111749579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122464339885344353191995509 11481031864251033111749579)
                ·
                  refine ⟨17221547796376549667624369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11481031864251033111749579 17221547796376549667624369)
                  ·
                    refine ⟨12916160847282412250718277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17221547796376549667624369 12916160847282412250718277)
                    ·
                      refine ⟨2421780158865452297009677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12916160847282412250718277 2421780158865452297009677)
                      ·
                        rfl

theorem cell23_4716400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_4716400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716400 prefixEnd_4716400 := by exact prefixLift 4716400
  have htrace : WordTrace (prefixWord ++ tailWord_4716400) baseStart_4716400 baseEnd_4716400 := by
    simpa [prefixWord, tailWord_4716400, baseEnd_4716400] using wordTrace_append hprefix tailTrace_4716400
  have hstable : (prefixWord ++ tailWord_4716400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716400).length < 2 ^ (prefixWord ++ tailWord_4716400).sum := by decide
  have hdescent : baseEnd_4716400 < baseStart_4716400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716414 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4716414 : Nat := 118140960795 + 4716414 * 2 ^ 59
def prefixEnd_4716414 : Nat := 4983230072969 + 3 ^ 40 * 4716414 * 2
def baseEnd_4716414 : Nat := 807262449198205080744871

theorem tailTrace_4716414 : CollatzResearch.WordTrace tailWord_4716414 prefixEnd_4716414 807262449198205080744871 := by
  unfold tailWord_4716414
  simp only [CollatzResearch.WordTrace]
  refine ⟨21502718841905631528403537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114681167156830034818152197 21502718841905631528403537)
  ·
    refine ⟨16127039131429223646302653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21502718841905631528403537 16127039131429223646302653)
    ·
      refine ⟨6047639674285958867363495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16127039131429223646302653 6047639674285958867363495)
      ·
        refine ⟨9071459511428938301045243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6047639674285958867363495 9071459511428938301045243)
        ·
          refine ⟨13607189267143407451567865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9071459511428938301045243 13607189267143407451567865)
          ·
            refine ⟨10205391950357555588675899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13607189267143407451567865 10205391950357555588675899)
            ·
              refine ⟨15308087925536333383013849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10205391950357555588675899 15308087925536333383013849)
              ·
                refine ⟨11481065944152250037260387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15308087925536333383013849 11481065944152250037260387)
                ·
                  refine ⟨17221598916228375055890581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11481065944152250037260387 17221598916228375055890581)
                  ·
                    refine ⟨807262449198205080744871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17221598916228375055890581 807262449198205080744871)
                    ·
                      rfl

theorem cell23_4716414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4716414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716414 prefixEnd_4716414 := by exact prefixLift 4716414
  have htrace : WordTrace (prefixWord ++ tailWord_4716414) baseStart_4716414 baseEnd_4716414 := by
    simpa [prefixWord, tailWord_4716414, baseEnd_4716414] using wordTrace_append hprefix tailTrace_4716414
  have hstable : (prefixWord ++ tailWord_4716414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716414).length < 2 ^ (prefixWord ++ tailWord_4716414).sum := by decide
  have hdescent : baseEnd_4716414 < baseStart_4716414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716421 : List Nat := [1, 3, 1, 1, 3, 2, 2, 5, 1, 2, 2]
def baseStart_4716421 : Nat := 118140960795 + 4716421 * 2 ^ 59
def prefixEnd_4716421 : Nat := 4983230072969 + 3 ^ 40 * 4716421 * 2
def baseEnd_4716421 : Nat := 2421790941959196714847081

theorem tailTrace_4716421 : CollatzResearch.WordTrace tailWord_4716421 prefixEnd_4716421 2421790941959196714847081 := by
  unfold tailWord_4716421
  simp only [CollatzResearch.WordTrace]
  refine ⟨172022006046219692422733117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114681337364146461615155411 172022006046219692422733117)
  ·
    refine ⟨64508252267332384658524919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172022006046219692422733117 64508252267332384658524919)
    ·
      refine ⟨96762378400998576987787379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64508252267332384658524919 96762378400998576987787379)
      ·
        refine ⟨145143567601497865481681069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96762378400998576987787379 145143567601497865481681069)
        ·
          refine ⟨54428837850561699555630401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145143567601497865481681069 54428837850561699555630401)
          ·
            refine ⟨40821628387921274666722801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54428837850561699555630401 40821628387921274666722801)
            ·
              refine ⟨30616221290940956000042101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40821628387921274666722801 30616221290940956000042101)
              ·
                refine ⟨2870270746025714625003947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30616221290940956000042101 2870270746025714625003947)
                ·
                  refine ⟨4305406119038571937505921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870270746025714625003947 4305406119038571937505921)
                  ·
                    refine ⟨3229054589278928953129441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4305406119038571937505921 3229054589278928953129441)
                    ·
                      refine ⟨2421790941959196714847081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229054589278928953129441 2421790941959196714847081)
                      ·
                        rfl

theorem cell23_4716421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_4716421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716421 prefixEnd_4716421 := by exact prefixLift 4716421
  have htrace : WordTrace (prefixWord ++ tailWord_4716421) baseStart_4716421 baseEnd_4716421 := by
    simpa [prefixWord, tailWord_4716421, baseEnd_4716421] using wordTrace_append hprefix tailTrace_4716421
  have hstable : (prefixWord ++ tailWord_4716421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716421).length < 2 ^ (prefixWord ++ tailWord_4716421).sum := by decide
  have hdescent : baseEnd_4716421 < baseStart_4716421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716424 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4716424 : Nat := 118140960795 + 4716424 * 2 ^ 59
def prefixEnd_4716424 : Nat := 4983230072969 + 3 ^ 40 * 4716424 * 2
def baseEnd_4716424 : Nat := 2421792482401160203109567

theorem tailTrace_4716424 : CollatzResearch.WordTrace tailWord_4716424 prefixEnd_4716424 2421792482401160203109567 := by
  unfold tailWord_4716424
  simp only [CollatzResearch.WordTrace]
  refine ⟨86011057732604411967546163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114681410310139215956728217 86011057732604411967546163)
  ·
    refine ⟨129016586598906617951319245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86011057732604411967546163 129016586598906617951319245)
    ·
      refine ⟨48381219974589981731744717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129016586598906617951319245 48381219974589981731744717)
      ·
        refine ⟨18142957490471243149404269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48381219974589981731744717 18142957490471243149404269)
        ·
          refine ⟨6803609058926716181026601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18142957490471243149404269 6803609058926716181026601)
          ·
            refine ⟨5102706794195037135769951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6803609058926716181026601 5102706794195037135769951)
            ·
              refine ⟨7654060191292555703654927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102706794195037135769951 7654060191292555703654927)
              ·
                refine ⟨11481090286938833555482391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7654060191292555703654927 11481090286938833555482391)
                ·
                  refine ⟨17221635430408250333223587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11481090286938833555482391 17221635430408250333223587)
                  ·
                    refine ⟨25832453145612375499835381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17221635430408250333223587 25832453145612375499835381)
                    ·
                      refine ⟨2421792482401160203109567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25832453145612375499835381 2421792482401160203109567)
                      ·
                        rfl

theorem cell23_4716424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4716424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716424 prefixEnd_4716424 := by exact prefixLift 4716424
  have htrace : WordTrace (prefixWord ++ tailWord_4716424) baseStart_4716424 baseEnd_4716424 := by
    simpa [prefixWord, tailWord_4716424, baseEnd_4716424] using wordTrace_append hprefix tailTrace_4716424
  have hstable : (prefixWord ++ tailWord_4716424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716424).length < 2 ^ (prefixWord ++ tailWord_4716424).sum := by decide
  have hdescent : baseEnd_4716424 < baseStart_4716424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716480 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_4716480 : Nat := 118140960795 + 4716480 * 2 ^ 59
def prefixEnd_4716480 : Nat := 4983230072969 + 3 ^ 40 * 4716480 * 2
def baseEnd_4716480 : Nat := 2421821237317811984009309

theorem tailTrace_4716480 : CollatzResearch.WordTrace tailWord_4716480 prefixEnd_4716480 2421821237317811984009309 := by
  unfold tailWord_4716480
  simp only [CollatzResearch.WordTrace]
  refine ⟨86012078976502972749565447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114682771968670630332753929 86012078976502972749565447)
  ·
    refine ⟨129018118464754459124348171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86012078976502972749565447 129018118464754459124348171)
    ·
      refine ⟨193527177697131688686522257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129018118464754459124348171 193527177697131688686522257)
      ·
        refine ⟨145145383272848766514891693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193527177697131688686522257 145145383272848766514891693)
        ·
          refine ⟨54429518727318287443084385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145145383272848766514891693 54429518727318287443084385)
          ·
            refine ⟨40822139045488715582313289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54429518727318287443084385 40822139045488715582313289)
            ·
              refine ⟨30616604284116536686734967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40822139045488715582313289 30616604284116536686734967)
              ·
                refine ⟨45924906426174805030102451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30616604284116536686734967 45924906426174805030102451)
                ·
                  refine ⟨68887359639262207545153677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45924906426174805030102451 68887359639262207545153677)
                  ·
                    refine ⟨25832759864723327829432629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68887359639262207545153677 25832759864723327829432629)
                    ·
                      refine ⟨2421821237317811984009309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25832759864723327829432629 2421821237317811984009309)
                      ·
                        rfl

theorem cell23_4716480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_4716480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716480 prefixEnd_4716480 := by exact prefixLift 4716480
  have htrace : WordTrace (prefixWord ++ tailWord_4716480) baseStart_4716480 baseEnd_4716480 := by
    simpa [prefixWord, tailWord_4716480, baseEnd_4716480] using wordTrace_append hprefix tailTrace_4716480
  have hstable : (prefixWord ++ tailWord_4716480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716480).length < 2 ^ (prefixWord ++ tailWord_4716480).sum := by decide
  have hdescent : baseEnd_4716480 < baseStart_4716480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716511 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 1, 4, 2]
def baseStart_4716511 : Nat := 118140960795 + 4716511 * 2 ^ 59
def prefixEnd_4716511 : Nat := 4983230072969 + 3 ^ 40 * 4716511 * 2
def baseEnd_4716511 : Nat := 2421837155218101362721667

theorem tailTrace_4716511 : CollatzResearch.WordTrace tailWord_4716511 prefixEnd_4716511 2421837155218101362721667 := by
  unfold tailWord_4716511
  simp only [CollatzResearch.WordTrace]
  refine ⟨172025288615893637793509387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114683525743929091862339591 172025288615893637793509387)
  ·
    refine ⟨258037932923840456690264081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172025288615893637793509387 258037932923840456690264081)
    ·
      refine ⟨193528449692880342517698061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258037932923840456690264081 193528449692880342517698061)
      ·
        refine ⟨72573168634830128444136773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193528449692880342517698061 72573168634830128444136773)
        ·
          refine ⟨13607469119030649083275645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72573168634830128444136773 13607469119030649083275645)
          ·
            refine ⟨5102800919636493406228367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13607469119030649083275645 5102800919636493406228367)
            ·
              refine ⟨7654201379454740109342551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102800919636493406228367 7654201379454740109342551)
              ·
                refine ⟨11481302069182110164013827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7654201379454740109342551 11481302069182110164013827)
                ·
                  refine ⟨17221953103773165246020741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11481302069182110164013827 17221953103773165246020741)
                  ·
                    refine ⟨3229116206957468483628889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17221953103773165246020741 3229116206957468483628889)
                    ·
                      refine ⟨2421837155218101362721667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229116206957468483628889 2421837155218101362721667)
                      ·
                        rfl

theorem cell23_4716511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_4716511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716511 prefixEnd_4716511 := by exact prefixLift 4716511
  have htrace : WordTrace (prefixWord ++ tailWord_4716511) baseStart_4716511 baseEnd_4716511 := by
    simpa [prefixWord, tailWord_4716511, baseEnd_4716511] using wordTrace_append hprefix tailTrace_4716511
  have hstable : (prefixWord ++ tailWord_4716511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716511).length < 2 ^ (prefixWord ++ tailWord_4716511).sum := by decide
  have hdescent : baseEnd_4716511 < baseStart_4716511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716551 : List Nat := [1, 1, 4, 3, 1, 3, 3, 2, 5]
def baseStart_4716551 : Nat := 118140960795 + 4716551 * 2 ^ 59
def prefixEnd_4716551 : Nat := 4983230072969 + 3 ^ 40 * 4716551 * 2
def baseEnd_4716551 : Nat := 269095299382697911802387

theorem tailTrace_4716551 : CollatzResearch.WordTrace tailWord_4716551 prefixEnd_4716551 269095299382697911802387 := by
  unfold tailWord_4716551
  simp only [CollatzResearch.WordTrace]
  refine ⟨172026747535748724624965507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114684498357165816416643671 172026747535748724624965507)
  ·
    refine ⟨258040121303623086937448261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172026747535748724624965507 258040121303623086937448261)
    ·
      refine ⟨48382522744429328800771549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258040121303623086937448261 48382522744429328800771549)
      ·
        refine ⟨18143446029160998300289331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48382522744429328800771549 18143446029160998300289331)
        ·
          refine ⟨27215169043741497450433997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18143446029160998300289331 27215169043741497450433997)
          ·
            refine ⟨10205688391403061543912749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27215169043741497450433997 10205688391403061543912749)
            ·
              refine ⟨3827133146776148078967281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10205688391403061543912749 3827133146776148078967281)
              ·
                refine ⟨2870349860082111059225461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3827133146776148078967281 2870349860082111059225461)
                ·
                  refine ⟨269095299382697911802387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2870349860082111059225461 269095299382697911802387)
                  ·
                    rfl

theorem cell23_4716551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 5].length) (baseStart_4716551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716551 prefixEnd_4716551 := by exact prefixLift 4716551
  have htrace : WordTrace (prefixWord ++ tailWord_4716551) baseStart_4716551 baseEnd_4716551 := by
    simpa [prefixWord, tailWord_4716551, baseEnd_4716551] using wordTrace_append hprefix tailTrace_4716551
  have hstable : (prefixWord ++ tailWord_4716551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716551).length < 2 ^ (prefixWord ++ tailWord_4716551).sum := by decide
  have hdescent : baseEnd_4716551 < baseStart_4716551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716604 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_4716604 : Nat := 118140960795 + 4716604 * 2 ^ 59
def prefixEnd_4716604 : Nat := 4983230072969 + 3 ^ 40 * 4716604 * 2
def baseEnd_4716604 : Nat := 2421884908918969498858739

theorem tailTrace_4716604 : CollatzResearch.WordTrace tailWord_4716604 prefixEnd_4716604 2421884908918969498858739 := by
  unfold tailWord_4716604
  simp only [CollatzResearch.WordTrace]
  refine ⟨86014340302278357338322433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114685787069704476451096577 86014340302278357338322433)
  ·
    refine ⟨64510755226708768003741825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86014340302278357338322433 64510755226708768003741825)
    ·
      refine ⟨48383066420031576002806369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64510755226708768003741825 48383066420031576002806369)
      ·
        refine ⟨36287299815023682002104777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48383066420031576002806369 36287299815023682002104777)
        ·
          refine ⟨27215474861267761501578583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36287299815023682002104777 27215474861267761501578583)
          ·
            refine ⟨40823212291901642252367875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27215474861267761501578583 40823212291901642252367875)
            ·
              refine ⟨61234818437852463378551813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40823212291901642252367875 61234818437852463378551813)
              ·
                refine ⟨11481528457097336883478465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61234818437852463378551813 11481528457097336883478465)
                ·
                  refine ⟨8611146342823002662608849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11481528457097336883478465 8611146342823002662608849)
                  ·
                    refine ⟨6458359757117251996956637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8611146342823002662608849 6458359757117251996956637)
                    ·
                      refine ⟨2421884908918969498858739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6458359757117251996956637 2421884908918969498858739)
                      ·
                        rfl

theorem cell23_4716604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_4716604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716604 prefixEnd_4716604 := by exact prefixLift 4716604
  have htrace : WordTrace (prefixWord ++ tailWord_4716604) baseStart_4716604 baseEnd_4716604 := by
    simpa [prefixWord, tailWord_4716604, baseEnd_4716604] using wordTrace_append hprefix tailTrace_4716604
  have hstable : (prefixWord ++ tailWord_4716604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716604).length < 2 ^ (prefixWord ++ tailWord_4716604).sum := by decide
  have hdescent : baseEnd_4716604 < baseStart_4716604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716607 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 6]
def baseStart_4716607 : Nat := 118140960795 + 4716607 * 2 ^ 59
def prefixEnd_4716607 : Nat := 4983230072969 + 3 ^ 40 * 4716607 * 2
def baseEnd_4716607 : Nat := 269098494373436998569025

theorem tailTrace_4716607 : CollatzResearch.WordTrace tailWord_4716607 prefixEnd_4716607 269098494373436998569025 := by
  unfold tailWord_4716607
  simp only [CollatzResearch.WordTrace]
  refine ⟨172028790023545846189004075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114685860015697230792669383 172028790023545846189004075)
  ·
    refine ⟨258043185035318769283506113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172028790023545846189004075 258043185035318769283506113)
    ·
      refine ⟨193532388776489076962629585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258043185035318769283506113 193532388776489076962629585)
      ·
        refine ⟨145149291582366807721972189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193532388776489076962629585 145149291582366807721972189)
        ·
          refine ⟨54430984343387552895739571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145149291582366807721972189 54430984343387552895739571)
          ·
            refine ⟨81646476515081329343609357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54430984343387552895739571 81646476515081329343609357)
            ·
              refine ⟨30617428693155498503853509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81646476515081329343609357 30617428693155498503853509)
              ·
                refine ⟨5740767879966655969472533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30617428693155498503853509 5740767879966655969472533)
                ·
                  refine ⟨269098494373436998569025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5740767879966655969472533 269098494373436998569025)
                  ·
                    rfl

theorem cell23_4716607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 6].length) (baseStart_4716607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716607 prefixEnd_4716607 := by exact prefixLift 4716607
  have htrace : WordTrace (prefixWord ++ tailWord_4716607) baseStart_4716607 baseEnd_4716607 := by
    simpa [prefixWord, tailWord_4716607, baseEnd_4716607] using wordTrace_append hprefix tailTrace_4716607
  have hstable : (prefixWord ++ tailWord_4716607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716607).length < 2 ^ (prefixWord ++ tailWord_4716607).sum := by decide
  have hdescent : baseEnd_4716607 < baseStart_4716607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716668 : List Nat := [2, 2, 2, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_4716668 : Nat := 118140960795 + 4716668 * 2 ^ 59
def prefixEnd_4716668 : Nat := 4983230072969 + 3 ^ 40 * 4716668 * 2
def baseEnd_4716668 : Nat := 2421917771680857248458445

theorem tailTrace_4716668 : CollatzResearch.WordTrace tailWord_4716668 prefixEnd_4716668 2421917771680857248458445 := by
  unfold tailWord_4716668
  simp only [CollatzResearch.WordTrace]
  refine ⟨86015507438162426803487329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114687343250883235737983105 86015507438162426803487329)
  ·
    refine ⟨64511630578621820102615497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86015507438162426803487329 64511630578621820102615497)
    ·
      refine ⟨48383722933966365076961623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64511630578621820102615497 48383722933966365076961623)
      ·
        refine ⟨72575584400949547615442435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48383722933966365076961623 72575584400949547615442435)
        ·
          refine ⟨108863376601424321423163653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72575584400949547615442435 108863376601424321423163653)
          ·
            refine ⟨20411883112767060266843185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108863376601424321423163653 20411883112767060266843185)
            ·
              refine ⟨15308912334575295200132389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20411883112767060266843185 15308912334575295200132389)
              ·
                refine ⟨2870421062732867850024823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15308912334575295200132389 2870421062732867850024823)
                ·
                  refine ⟨4305631594099301775037235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870421062732867850024823 4305631594099301775037235)
                  ·
                    refine ⟨6458447391148952662555853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4305631594099301775037235 6458447391148952662555853)
                    ·
                      refine ⟨2421917771680857248458445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6458447391148952662555853 2421917771680857248458445)
                      ·
                        rfl

theorem cell23_4716668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_4716668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716668 prefixEnd_4716668 := by exact prefixLift 4716668
  have htrace : WordTrace (prefixWord ++ tailWord_4716668) baseStart_4716668 baseEnd_4716668 := by
    simpa [prefixWord, tailWord_4716668, baseEnd_4716668] using wordTrace_append hprefix tailTrace_4716668
  have hstable : (prefixWord ++ tailWord_4716668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716668).length < 2 ^ (prefixWord ++ tailWord_4716668).sum := by decide
  have hdescent : baseEnd_4716668 < baseStart_4716668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716738 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4716738 : Nat := 118140960795 + 4716738 * 2 ^ 59
def prefixEnd_4716738 : Nat := 4983230072969 + 3 ^ 40 * 4716738 * 2
def baseEnd_4716738 : Nat := 2421953715326671974583123

theorem tailTrace_4716738 : CollatzResearch.WordTrace tailWord_4716738 prefixEnd_4716738 2421953715326671974583123 := by
  unfold tailWord_4716738
  simp only [CollatzResearch.WordTrace]
  refine ⟨43008391996517813890505717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114689045324047503708015245 43008391996517813890505717)
  ·
    refine ⟨4032036749673545052234911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43008391996517813890505717 4032036749673545052234911)
    ·
      refine ⟨6048055124510317578352367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4032036749673545052234911 6048055124510317578352367)
      ·
        refine ⟨9072082686765476367528551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6048055124510317578352367 9072082686765476367528551)
        ·
          refine ⟨13608124030148214551292827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072082686765476367528551 13608124030148214551292827)
          ·
            refine ⟨20412186045222321826939241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608124030148214551292827 20412186045222321826939241)
            ·
              refine ⟨15309139533916741370204431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20412186045222321826939241 15309139533916741370204431)
              ·
                refine ⟨22963709300875112055306647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15309139533916741370204431 22963709300875112055306647)
                ·
                  refine ⟨34445563951312668082959971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22963709300875112055306647 34445563951312668082959971)
                  ·
                    refine ⟨51668345926969002124439957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34445563951312668082959971 51668345926969002124439957)
                    ·
                      refine ⟨2421953715326671974583123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51668345926969002124439957 2421953715326671974583123)
                      ·
                        rfl

theorem cell23_4716738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4716738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716738 prefixEnd_4716738 := by exact prefixLift 4716738
  have htrace : WordTrace (prefixWord ++ tailWord_4716738) baseStart_4716738 baseEnd_4716738 := by
    simpa [prefixWord, tailWord_4716738, baseEnd_4716738] using wordTrace_append hprefix tailTrace_4716738
  have hstable : (prefixWord ++ tailWord_4716738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716738).length < 2 ^ (prefixWord ++ tailWord_4716738).sum := by decide
  have hdescent : baseEnd_4716738 < baseStart_4716738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716751 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 3, 3, 2]
def baseStart_4716751 : Nat := 118140960795 + 4716751 * 2 ^ 59
def prefixEnd_4716751 : Nat := 4983230072969 + 3 ^ 40 * 4716751 * 2
def baseEnd_4716751 : Nat := 2421960390575180423720563

theorem tailTrace_4716751 : CollatzResearch.WordTrace tailWord_4716751 prefixEnd_4716751 2421960390575180423720563 := by
  unfold tailWord_4716751
  simp only [CollatzResearch.WordTrace]
  refine ⟨172034042135024158782246107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114689361423349439188164071 172034042135024158782246107)
  ·
    refine ⟨258051063202536238173369161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172034042135024158782246107 258051063202536238173369161)
    ·
      refine ⟨193538297401902178630026871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258051063202536238173369161 193538297401902178630026871)
      ·
        refine ⟨290307446102853267945040307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193538297401902178630026871 290307446102853267945040307)
        ·
          refine ⟨435461169154279901917560461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290307446102853267945040307 435461169154279901917560461)
          ·
            refine ⟨163297938432854963219085173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 435461169154279901917560461 163297938432854963219085173)
            ·
              refine ⟨15309181728080152801789235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163297938432854963219085173 15309181728080152801789235)
              ·
                refine ⟨22963772592120229202683853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15309181728080152801789235 22963772592120229202683853)
                ·
                  refine ⟨8611414722045085951006445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22963772592120229202683853 8611414722045085951006445)
                  ·
                    refine ⟨3229280520766907231627417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8611414722045085951006445 3229280520766907231627417)
                    ·
                      refine ⟨2421960390575180423720563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229280520766907231627417 2421960390575180423720563)
                      ·
                        rfl

theorem cell23_4716751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3, 2].length) (baseStart_4716751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716751 prefixEnd_4716751 := by exact prefixLift 4716751
  have htrace : WordTrace (prefixWord ++ tailWord_4716751) baseStart_4716751 baseEnd_4716751 := by
    simpa [prefixWord, tailWord_4716751, baseEnd_4716751] using wordTrace_append hprefix tailTrace_4716751
  have hstable : (prefixWord ++ tailWord_4716751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716751).length < 2 ^ (prefixWord ++ tailWord_4716751).sum := by decide
  have hdescent : baseEnd_4716751 < baseStart_4716751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716758 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4716758 : Nat := 118140960795 + 4716758 * 2 ^ 59
def prefixEnd_4716758 : Nat := 4983230072969 + 3 ^ 40 * 4716758 * 2
def baseEnd_4716758 : Nat := 2421963984939761896333031

theorem tailTrace_4716758 : CollatzResearch.WordTrace tailWord_4716758 prefixEnd_4716758 2421963984939761896333031 := by
  unfold tailWord_4716758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752143590374924936109433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114689531630665865985167285 10752143590374924936109433)
  ·
    refine ⟨8064107692781193702082075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10752143590374924936109433 8064107692781193702082075)
    ·
      refine ⟨12096161539171790553123113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8064107692781193702082075 12096161539171790553123113)
      ·
        refine ⟨9072121154378842914842335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12096161539171790553123113 9072121154378842914842335)
        ·
          refine ⟨13608181731568264372263503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072121154378842914842335 13608181731568264372263503)
          ·
            refine ⟨20412272597352396558395255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608181731568264372263503 20412272597352396558395255)
            ·
              refine ⟨30618408896028594837592883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20412272597352396558395255 30618408896028594837592883)
              ·
                refine ⟨45927613344042892256389325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30618408896028594837592883 45927613344042892256389325)
                ·
                  refine ⟨17222855004016084596145997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45927613344042892256389325 17222855004016084596145997)
                  ·
                    refine ⟨6458570626506031723554749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17222855004016084596145997 6458570626506031723554749)
                    ·
                      refine ⟨2421963984939761896333031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6458570626506031723554749 2421963984939761896333031)
                      ·
                        rfl

theorem cell23_4716758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4716758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716758 prefixEnd_4716758 := by exact prefixLift 4716758
  have htrace : WordTrace (prefixWord ++ tailWord_4716758) baseStart_4716758 baseEnd_4716758 := by
    simpa [prefixWord, tailWord_4716758, baseEnd_4716758] using wordTrace_append hprefix tailTrace_4716758
  have hstable : (prefixWord ++ tailWord_4716758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716758).length < 2 ^ (prefixWord ++ tailWord_4716758).sum := by decide
  have hdescent : baseEnd_4716758 < baseStart_4716758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716775 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4716775 : Nat := 118140960795 + 4716775 * 2 ^ 59
def prefixEnd_4716775 : Nat := 4983230072969 + 3 ^ 40 * 4716775 * 2
def baseEnd_4716775 : Nat := 2421972714110888329820453

theorem tailTrace_4716775 : CollatzResearch.WordTrace tailWord_4716775 prefixEnd_4716775 2421972714110888329820453 := by
  unfold tailWord_4716775
  simp only [CollatzResearch.WordTrace]
  refine ⟨172034917486937210881119779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114689944991291473920746519 172034917486937210881119779)
  ·
    refine ⟨258052376230405816321679669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172034917486937210881119779 258052376230405816321679669)
    ·
      refine ⟨24192410271600545280157469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 258052376230405816321679669 24192410271600545280157469)
      ·
        refine ⟨9072153851850204480059051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24192410271600545280157469 9072153851850204480059051)
        ·
          refine ⟨13608230777775306720088577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072153851850204480059051 13608230777775306720088577)
          ·
            refine ⟨10206173083331480040066433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13608230777775306720088577 10206173083331480040066433)
            ·
              refine ⟨7654629812498610030049825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10206173083331480040066433 7654629812498610030049825)
              ·
                refine ⟨5740972359373957522537369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7654629812498610030049825 5740972359373957522537369)
                ·
                  refine ⟨4305729269530468141903027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5740972359373957522537369 4305729269530468141903027)
                  ·
                    refine ⟨6458593904295702212854541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4305729269530468141903027 6458593904295702212854541)
                    ·
                      refine ⟨2421972714110888329820453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6458593904295702212854541 2421972714110888329820453)
                      ·
                        rfl

theorem cell23_4716775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4716775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716775 prefixEnd_4716775 := by exact prefixLift 4716775
  have htrace : WordTrace (prefixWord ++ tailWord_4716775) baseStart_4716775 baseEnd_4716775 := by
    simpa [prefixWord, tailWord_4716775, baseEnd_4716775] using wordTrace_append hprefix tailTrace_4716775
  have hstable : (prefixWord ++ tailWord_4716775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716775).length < 2 ^ (prefixWord ++ tailWord_4716775).sum := by decide
  have hdescent : baseEnd_4716775 < baseStart_4716775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716794 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_4716794 : Nat := 118140960795 + 4716794 * 2 ^ 59
def prefixEnd_4716794 : Nat := 4983230072969 + 3 ^ 40 * 4716794 * 2
def baseEnd_4716794 : Nat := 2421982470243323755482865

theorem tailTrace_4716794 : CollatzResearch.WordTrace tailWord_4716794 prefixEnd_4716794 2421982470243323755482865 := by
  unfold tailWord_4716794
  simp only [CollatzResearch.WordTrace]
  refine ⟨43008902618467094281515359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114690406982578918084040957 43008902618467094281515359)
  ·
    refine ⟨64513353927700641422273039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43008902618467094281515359 64513353927700641422273039)
    ·
      refine ⟨96770030891550962133409559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64513353927700641422273039 96770030891550962133409559)
      ·
        refine ⟨145155046337326443200114339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96770030891550962133409559 145155046337326443200114339)
        ·
          refine ⟨217732569505989664800171509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145155046337326443200114339 217732569505989664800171509)
          ·
            refine ⟨20412428391186531075016079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217732569505989664800171509 20412428391186531075016079)
            ·
              refine ⟨30618642586779796612524119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20412428391186531075016079 30618642586779796612524119)
              ·
                refine ⟨45927963880169694918786179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30618642586779796612524119 45927963880169694918786179)
                ·
                  refine ⟨68891945820254542378179269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45927963880169694918786179 68891945820254542378179269)
                  ·
                    refine ⟨12917239841297726695908613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68891945820254542378179269 12917239841297726695908613)
                    ·
                      refine ⟨2421982470243323755482865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12917239841297726695908613 2421982470243323755482865)
                      ·
                        rfl

theorem cell23_4716794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_4716794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716794 prefixEnd_4716794 := by exact prefixLift 4716794
  have htrace : WordTrace (prefixWord ++ tailWord_4716794) baseStart_4716794 baseEnd_4716794 := by
    simpa [prefixWord, tailWord_4716794, baseEnd_4716794] using wordTrace_append hprefix tailTrace_4716794
  have hstable : (prefixWord ++ tailWord_4716794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716794).length < 2 ^ (prefixWord ++ tailWord_4716794).sum := by decide
  have hdescent : baseEnd_4716794 < baseStart_4716794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716821 : List Nat := [1, 3, 2, 1, 2, 1, 3, 5, 5]
def baseStart_4716821 : Nat := 118140960795 + 4716821 * 2 ^ 59
def prefixEnd_4716821 : Nat := 4983230072969 + 3 ^ 40 * 4716821 * 2
def baseEnd_4716821 : Nat := 269110703802332794427249

theorem tailTrace_4716821 : CollatzResearch.WordTrace tailWord_4716821 prefixEnd_4716821 269110703802332794427249 := by
  unfold tailWord_4716821
  simp only [CollatzResearch.WordTrace]
  refine ⟨172036595244770560737294317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114691063496513707158196211 172036595244770560737294317)
  ·
    refine ⟨64513723216788960276485369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172036595244770560737294317 64513723216788960276485369)
    ·
      refine ⟨48385292412591720207364027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64513723216788960276485369 48385292412591720207364027)
      ·
        refine ⟨72577938618887580311046041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48385292412591720207364027 72577938618887580311046041)
        ·
          refine ⟨54433453964165685233284531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72577938618887580311046041 54433453964165685233284531)
          ·
            refine ⟨81650180946248527849926797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54433453964165685233284531 81650180946248527849926797)
            ·
              refine ⟨30618817854843197943722549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81650180946248527849926797 30618817854843197943722549)
              ·
                refine ⟨2870514173891549807223989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30618817854843197943722549 2870514173891549807223989)
                ·
                  refine ⟨269110703802332794427249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2870514173891549807223989 269110703802332794427249)
                  ·
                    rfl

theorem cell23_4716821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_4716821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716821 prefixEnd_4716821 := by exact prefixLift 4716821
  have htrace : WordTrace (prefixWord ++ tailWord_4716821) baseStart_4716821 baseEnd_4716821 := by
    simpa [prefixWord, tailWord_4716821, baseEnd_4716821] using wordTrace_append hprefix tailTrace_4716821
  have hstable : (prefixWord ++ tailWord_4716821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716821).length < 2 ^ (prefixWord ++ tailWord_4716821).sum := by decide
  have hdescent : baseEnd_4716821 < baseStart_4716821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716831 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 3]
def baseStart_4716831 : Nat := 118140960795 + 4716831 * 2 ^ 59
def prefixEnd_4716831 : Nat := 4983230072969 + 3 ^ 40 * 4716831 * 2
def baseEnd_4716831 : Nat := 2422001469027540110720195

theorem tailTrace_4716831 : CollatzResearch.WordTrace tailWord_4716831 prefixEnd_4716831 2422001469027540110720195 := by
  unfold tailWord_4716831
  simp only [CollatzResearch.WordTrace]
  refine ⟨172036959974734332445158347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114691306649822888296772231 172036959974734332445158347)
  ·
    refine ⟨258055439962101498667737521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172036959974734332445158347 258055439962101498667737521)
    ·
      refine ⟨193541579971576124000803141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258055439962101498667737521 193541579971576124000803141)
      ·
        refine ⟨36289046244670523250150589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193541579971576124000803141 36289046244670523250150589)
        ·
          refine ⟨13608392341751446218806471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36289046244670523250150589 13608392341751446218806471)
          ·
            refine ⟨20412588512627169328209707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608392341751446218806471 20412588512627169328209707)
            ·
              refine ⟨30618882768940753992314561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20412588512627169328209707 30618882768940753992314561)
              ·
                refine ⟨22964162076705565494235921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30618882768940753992314561 22964162076705565494235921)
                ·
                  refine ⟨17223121557529174120676941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22964162076705565494235921 17223121557529174120676941)
                  ·
                    refine ⟨6458670584073440295253853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17223121557529174120676941 6458670584073440295253853)
                    ·
                      refine ⟨2422001469027540110720195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6458670584073440295253853 2422001469027540110720195)
                      ·
                        rfl

theorem cell23_4716831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_4716831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716831 prefixEnd_4716831 := by exact prefixLift 4716831
  have htrace : WordTrace (prefixWord ++ tailWord_4716831) baseStart_4716831 baseEnd_4716831 := by
    simpa [prefixWord, tailWord_4716831, baseEnd_4716831] using wordTrace_append hprefix tailTrace_4716831
  have hstable : (prefixWord ++ tailWord_4716831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716831).length < 2 ^ (prefixWord ++ tailWord_4716831).sum := by decide
  have hdescent : baseEnd_4716831 < baseStart_4716831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716832 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 2, 2, 2]
def baseStart_4716832 : Nat := 118140960795 + 4716832 * 2 ^ 59
def prefixEnd_4716832 : Nat := 4983230072969 + 3 ^ 40 * 4716832 * 2
def baseEnd_4716832 : Nat := 2422001982508194606807691

theorem tailTrace_4716832 : CollatzResearch.WordTrace tailWord_4716832 prefixEnd_4716832 2422001982508194606807691 := by
  unfold tailWord_4716832
  simp only [CollatzResearch.WordTrace]
  refine ⟨86018498223865354807972375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114691330965153806410629833 86018498223865354807972375)
  ·
    refine ⟨129027747335798032211958563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86018498223865354807972375 129027747335798032211958563)
    ·
      refine ⟨193541621003697048317937845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129027747335798032211958563 193541621003697048317937845)
      ·
        refine ⟨18144526969096598279806673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193541621003697048317937845 18144526969096598279806673)
        ·
          refine ⟨13608395226822448709855005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18144526969096598279806673 13608395226822448709855005)
          ·
            refine ⟨5103148210058418266195627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13608395226822448709855005 5103148210058418266195627)
            ·
              refine ⟨7654722315087627399293441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103148210058418266195627 7654722315087627399293441)
              ·
                refine ⟨5741041736315720549470081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7654722315087627399293441 5741041736315720549470081)
                ·
                  refine ⟨4305781302236790412102561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5741041736315720549470081 4305781302236790412102561)
                  ·
                    refine ⟨3229335976677592809076921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4305781302236790412102561 3229335976677592809076921)
                    ·
                      refine ⟨2422001982508194606807691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229335976677592809076921 2422001982508194606807691)
                      ·
                        rfl

theorem cell23_4716832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_4716832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716832 prefixEnd_4716832 := by exact prefixLift 4716832
  have htrace : WordTrace (prefixWord ++ tailWord_4716832) baseStart_4716832 baseEnd_4716832 := by
    simpa [prefixWord, tailWord_4716832, baseEnd_4716832] using wordTrace_append hprefix tailTrace_4716832
  have hstable : (prefixWord ++ tailWord_4716832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716832).length < 2 ^ (prefixWord ++ tailWord_4716832).sum := by decide
  have hdescent : baseEnd_4716832 < baseStart_4716832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716844 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_4716844 : Nat := 118140960795 + 4716844 * 2 ^ 59
def prefixEnd_4716844 : Nat := 4983230072969 + 3 ^ 40 * 4716844 * 2
def baseEnd_4716844 : Nat := 2422008144276048559857635

theorem tailTrace_4716844 : CollatzResearch.WordTrace tailWord_4716844 prefixEnd_4716844 2422008144276048559857635 := by
  unfold tailWord_4716844
  simp only [CollatzResearch.WordTrace]
  refine ⟨86018717061843617832690793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114691622749124823776921057 86018717061843617832690793)
  ·
    refine ⟨64514037796382713374518095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86018717061843617832690793 64514037796382713374518095)
    ·
      refine ⟨96771056694574070061777143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64514037796382713374518095 96771056694574070061777143)
      ·
        refine ⟨145156585041861105092665715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96771056694574070061777143 145156585041861105092665715)
        ·
          refine ⟨217734877562791657638998573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145156585041861105092665715 217734877562791657638998573)
          ·
            refine ⟨81650579086046871614624465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217734877562791657638998573 81650579086046871614624465)
            ·
              refine ⟨61237934314535153710968349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81650579086046871614624465 61237934314535153710968349)
              ·
                refine ⟨22964225367950682641613131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61237934314535153710968349 22964225367950682641613131)
                ·
                  refine ⟨34446338051926023962419697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22964225367950682641613131 34446338051926023962419697)
                  ·
                    refine ⟨25834753538944517971814773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34446338051926023962419697 25834753538944517971814773)
                    ·
                      refine ⟨2422008144276048559857635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25834753538944517971814773 2422008144276048559857635)
                      ·
                        rfl

theorem cell23_4716844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_4716844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716844 prefixEnd_4716844 := by exact prefixLift 4716844
  have htrace : WordTrace (prefixWord ++ tailWord_4716844) baseStart_4716844 baseEnd_4716844 := by
    simpa [prefixWord, tailWord_4716844, baseEnd_4716844] using wordTrace_append hprefix tailTrace_4716844
  have hstable : (prefixWord ++ tailWord_4716844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716844).length < 2 ^ (prefixWord ++ tailWord_4716844).sum := by decide
  have hdescent : baseEnd_4716844 < baseStart_4716844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716871 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_4716871 : Nat := 118140960795 + 4716871 * 2 ^ 59
def prefixEnd_4716871 : Nat := 4983230072969 + 3 ^ 40 * 4716871 * 2
def baseEnd_4716871 : Nat := 2422022008253719954220011

theorem tailTrace_4716871 : CollatzResearch.WordTrace tailWord_4716871 prefixEnd_4716871 2422022008253719954220011 := by
  unfold tailWord_4716871
  simp only [CollatzResearch.WordTrace]
  refine ⟨172038418894589419276614467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114692279263059612851076311 172038418894589419276614467)
  ·
    refine ⟨258057628341884128914921701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172038418894589419276614467 258057628341884128914921701)
    ·
      refine ⟨48385805314103274171547819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258057628341884128914921701 48385805314103274171547819)
      ·
        refine ⟨72578707971154911257321729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48385805314103274171547819 72578707971154911257321729)
        ·
          refine ⟨54434030978366183442991297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72578707971154911257321729 54434030978366183442991297)
          ·
            refine ⟨40825523233774637582243473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54434030978366183442991297 40825523233774637582243473)
            ·
              refine ⟨30619142425330978186682605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40825523233774637582243473 30619142425330978186682605)
              ·
                refine ⟨11482178409499116820005977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30619142425330978186682605 11482178409499116820005977)
                ·
                  refine ⟨8611633807124337615004483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11482178409499116820005977 8611633807124337615004483)
                  ·
                    refine ⟨12917450710686506422506725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8611633807124337615004483 12917450710686506422506725)
                    ·
                      refine ⟨2422022008253719954220011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12917450710686506422506725 2422022008253719954220011)
                      ·
                        rfl

theorem cell23_4716871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_4716871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716871 prefixEnd_4716871 := by exact prefixLift 4716871
  have htrace : WordTrace (prefixWord ++ tailWord_4716871) baseStart_4716871 baseEnd_4716871 := by
    simpa [prefixWord, tailWord_4716871, baseEnd_4716871] using wordTrace_append hprefix tailTrace_4716871
  have hstable : (prefixWord ++ tailWord_4716871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716871).length < 2 ^ (prefixWord ++ tailWord_4716871).sum := by decide
  have hdescent : baseEnd_4716871 < baseStart_4716871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716874 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_4716874 : Nat := 118140960795 + 4716874 * 2 ^ 59
def prefixEnd_4716874 : Nat := 4983230072969 + 3 ^ 40 * 4716874 * 2
def baseEnd_4716874 : Nat := 2422023548695683442482497

theorem tailTrace_4716874 : CollatzResearch.WordTrace tailWord_4716874 prefixEnd_4716874 2422023548695683442482497 := by
  unfold tailWord_4716874
  simp only [CollatzResearch.WordTrace]
  refine ⟨43009632078394637697243419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114692352209052367192649117 43009632078394637697243419)
  ·
    refine ⟨64514448117591956545865129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43009632078394637697243419 64514448117591956545865129)
    ·
      refine ⟨48385836088193967409398847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64514448117591956545865129 48385836088193967409398847)
      ·
        refine ⟨72578754132290951114098271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48385836088193967409398847 72578754132290951114098271)
        ·
          refine ⟨108868131198436426671147407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72578754132290951114098271 108868131198436426671147407)
          ·
            refine ⟨163302196797654640006721111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108868131198436426671147407 163302196797654640006721111)
            ·
              refine ⟨244953295196481960010081667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163302196797654640006721111 244953295196481960010081667)
              ·
                refine ⟨367429942794722940015122501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244953295196481960010081667 367429942794722940015122501)
                ·
                  refine ⟨68893114274010551252835469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367429942794722940015122501 68893114274010551252835469)
                  ·
                    refine ⟨25834917852753956719813301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68893114274010551252835469 25834917852753956719813301)
                    ·
                      refine ⟨2422023548695683442482497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25834917852753956719813301 2422023548695683442482497)
                      ·
                        rfl

theorem cell23_4716874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_4716874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716874 prefixEnd_4716874 := by exact prefixLift 4716874
  have htrace : WordTrace (prefixWord ++ tailWord_4716874) baseStart_4716874 baseEnd_4716874 := by
    simpa [prefixWord, tailWord_4716874, baseEnd_4716874] using wordTrace_append hprefix tailTrace_4716874
  have hstable : (prefixWord ++ tailWord_4716874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716874).length < 2 ^ (prefixWord ++ tailWord_4716874).sum := by decide
  have hdescent : baseEnd_4716874 < baseStart_4716874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716978 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_4716978 : Nat := 118140960795 + 4716978 * 2 ^ 59
def prefixEnd_4716978 : Nat := 4983230072969 + 3 ^ 40 * 4716978 * 2
def baseEnd_4716978 : Nat := 2422076950683751035582019

theorem tailTrace_4716978 : CollatzResearch.WordTrace tailWord_4716978 prefixEnd_4716978 2422076950683751035582019 := by
  unfold tailWord_4716978
  simp only [CollatzResearch.WordTrace]
  refine ⟨43010580376300444137689897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114694881003467851033839725 43010580376300444137689897)
  ·
    refine ⟨32257935282225333103267423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43010580376300444137689897 32257935282225333103267423)
    ·
      refine ⟨48386902923337999654901135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32257935282225333103267423 48386902923337999654901135)
      ·
        refine ⟨72580354385006999482351703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48386902923337999654901135 72580354385006999482351703)
        ·
          refine ⟨108870531577510499223527555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72580354385006999482351703 108870531577510499223527555)
          ·
            refine ⟨163305797366265748835291333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108870531577510499223527555 163305797366265748835291333)
            ·
              refine ⟨30619837006174827906617125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163305797366265748835291333 30619837006174827906617125)
              ·
                refine ⟨5741219438657780232490711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30619837006174827906617125 5741219438657780232490711)
                ·
                  refine ⟨8611829157986670348736067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5741219438657780232490711 8611829157986670348736067)
                  ·
                    refine ⟨12917743736980005523104101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8611829157986670348736067 12917743736980005523104101)
                    ·
                      refine ⟨2422076950683751035582019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12917743736980005523104101 2422076950683751035582019)
                      ·
                        rfl

theorem cell23_4716978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_4716978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716978 prefixEnd_4716978 := by exact prefixLift 4716978
  have htrace : WordTrace (prefixWord ++ tailWord_4716978) baseStart_4716978 baseEnd_4716978 := by
    simpa [prefixWord, tailWord_4716978, baseEnd_4716978] using wordTrace_append hprefix tailTrace_4716978
  have hstable : (prefixWord ++ tailWord_4716978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716978).length < 2 ^ (prefixWord ++ tailWord_4716978).sum := by decide
  have hdescent : baseEnd_4716978 < baseStart_4716978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4716988 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_4716988 : Nat := 118140960795 + 4716988 * 2 ^ 59
def prefixEnd_4716988 : Nat := 4983230072969 + 3 ^ 40 * 4716988 * 2
def baseEnd_4716988 : Nat := 807360695163431998818991

theorem tailTrace_4716988 : CollatzResearch.WordTrace tailWord_4716988 prefixEnd_4716988 807360695163431998818991 := by
  unfold tailWord_4716988
  simp only [CollatzResearch.WordTrace]
  refine ⟨86021343117582774129311809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114695124156777032172415745 86021343117582774129311809)
  ·
    refine ⟨64516007338187080596983857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86021343117582774129311809 64516007338187080596983857)
    ·
      refine ⟨48387005503640310447737893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64516007338187080596983857 48387005503640310447737893)
      ·
        refine ⟨9072563531932558208950855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48387005503640310447737893 9072563531932558208950855)
        ·
          refine ⟨13608845297898837313426283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072563531932558208950855 13608845297898837313426283)
          ·
            refine ⟨20413267946848255970139425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608845297898837313426283 20413267946848255970139425)
            ·
              refine ⟨15309950960136191977604569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20413267946848255970139425 15309950960136191977604569)
              ·
                refine ⟨11482463220102143983203427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15309950960136191977604569 11482463220102143983203427)
                ·
                  refine ⟨17223694830153215974805141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11482463220102143983203427 17223694830153215974805141)
                  ·
                    refine ⟨807360695163431998818991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17223694830153215974805141 807360695163431998818991)
                    ·
                      rfl

theorem cell23_4716988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_4716988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4716988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4716988 prefixEnd_4716988 := by exact prefixLift 4716988
  have htrace : WordTrace (prefixWord ++ tailWord_4716988) baseStart_4716988 baseEnd_4716988 := by
    simpa [prefixWord, tailWord_4716988, baseEnd_4716988] using wordTrace_append hprefix tailTrace_4716988
  have hstable : (prefixWord ++ tailWord_4716988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4716988).length < 2 ^ (prefixWord ++ tailWord_4716988).sum := by decide
  have hdescent : baseEnd_4716988 < baseStart_4716988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4716988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717012 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_4717012 : Nat := 118140960795 + 4717012 * 2 ^ 59
def prefixEnd_4717012 : Nat := 4983230072969 + 3 ^ 40 * 4717012 * 2
def baseEnd_4717012 : Nat := 2422094409026003902556863

theorem tailTrace_4717012 : CollatzResearch.WordTrace tailWord_4717012 prefixEnd_4717012 2422094409026003902556863 := by
  unfold tailWord_4717012
  simp only [CollatzResearch.WordTrace]
  refine ⟨86021780793539300178748645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114695707724719066904998193 86021780793539300178748645)
  ·
    refine ⟨16129083898788618783515371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86021780793539300178748645 16129083898788618783515371)
    ·
      refine ⟨24193625848182928175273057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16129083898788618783515371 24193625848182928175273057)
      ·
        refine ⟨18145219386137196131454793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24193625848182928175273057 18145219386137196131454793)
        ·
          refine ⟨13608914539602897098591095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18145219386137196131454793 13608914539602897098591095)
          ·
            refine ⟨20413371809404345647886643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608914539602897098591095 20413371809404345647886643)
            ·
              refine ⟨30620057714106518471829965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20413371809404345647886643 30620057714106518471829965)
              ·
                refine ⟨11482521642789944426936237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30620057714106518471829965 11482521642789944426936237)
                ·
                  refine ⟨4305945616046229160101089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11482521642789944426936237 4305945616046229160101089)
                  ·
                    refine ⟨3229459212034671870075817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4305945616046229160101089 3229459212034671870075817)
                    ·
                      refine ⟨2422094409026003902556863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229459212034671870075817 2422094409026003902556863)
                      ·
                        rfl

theorem cell23_4717012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_4717012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717012 prefixEnd_4717012 := by exact prefixLift 4717012
  have htrace : WordTrace (prefixWord ++ tailWord_4717012) baseStart_4717012 baseEnd_4717012 := by
    simpa [prefixWord, tailWord_4717012, baseEnd_4717012] using wordTrace_append hprefix tailTrace_4717012
  have hstable : (prefixWord ++ tailWord_4717012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717012).length < 2 ^ (prefixWord ++ tailWord_4717012).sum := by decide
  have hdescent : baseEnd_4717012 < baseStart_4717012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717041 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_4717041 : Nat := 118140960795 + 4717041 * 2 ^ 59
def prefixEnd_4717041 : Nat := 4983230072969 + 3 ^ 40 * 4717041 * 2
def baseEnd_4717041 : Nat := 2422109299964984289094229

theorem tailTrace_4717041 : CollatzResearch.WordTrace tailWord_4717041 prefixEnd_4717041 2422109299964984289094229 := by
  unfold tailWord_4717041
  simp only [CollatzResearch.WordTrace]
  refine ⟨172044619303973538310302977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114696412869315692206868651 172044619303973538310302977)
  ·
    refine ⟨129033464477980153732727233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172044619303973538310302977 129033464477980153732727233)
    ·
      refine ⟨96775098358485115299545425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129033464477980153732727233 96775098358485115299545425)
      ·
        refine ⟨72581323768863836474659069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96775098358485115299545425 72581323768863836474659069)
        ·
          refine ⟨27217996413323938677997151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72581323768863836474659069 27217996413323938677997151)
          ·
            refine ⟨40826994619985908016995727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27217996413323938677997151 40826994619985908016995727)
            ·
              refine ⟨61240491929978862025493591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40826994619985908016995727 61240491929978862025493591)
              ·
                refine ⟨91860737894968293038240387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61240491929978862025493591 91860737894968293038240387)
                ·
                  refine ⟨137791106842452439557360581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91860737894968293038240387 137791106842452439557360581)
                  ·
                    refine ⟨25835832532959832417005109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137791106842452439557360581 25835832532959832417005109)
                    ·
                      refine ⟨2422109299964984289094229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25835832532959832417005109 2422109299964984289094229)
                      ·
                        rfl

theorem cell23_4717041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_4717041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717041 prefixEnd_4717041 := by exact prefixLift 4717041
  have htrace : WordTrace (prefixWord ++ tailWord_4717041) baseStart_4717041 baseEnd_4717041 := by
    simpa [prefixWord, tailWord_4717041, baseEnd_4717041] using wordTrace_append hprefix tailTrace_4717041
  have hstable : (prefixWord ++ tailWord_4717041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717041).length < 2 ^ (prefixWord ++ tailWord_4717041).sum := by decide
  have hdescent : baseEnd_4717041 < baseStart_4717041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717055 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 1, 3, 2]
def baseStart_4717055 : Nat := 118140960795 + 4717055 * 2 ^ 59
def prefixEnd_4717055 : Nat := 4983230072969 + 3 ^ 40 * 4717055 * 2
def baseEnd_4717055 : Nat := 2422116488694147234319165

theorem tailTrace_4717055 : CollatzResearch.WordTrace tailWord_4717055 prefixEnd_4717055 2422116488694147234319165 := by
  unfold tailWord_4717055
  simp only [CollatzResearch.WordTrace]
  refine ⟨172045129925922818701312619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114696753283948545800875079 172045129925922818701312619)
  ·
    refine ⟨258067694888884228051968929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172045129925922818701312619 258067694888884228051968929)
    ·
      refine ⟨193550771166663171038976697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258067694888884228051968929 193550771166663171038976697)
      ·
        refine ⟨145163078374997378279232523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193550771166663171038976697 145163078374997378279232523)
        ·
          refine ⟨217744617562496067418848785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145163078374997378279232523 217744617562496067418848785)
          ·
            refine ⟨163308463171872050564136589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217744617562496067418848785 163308463171872050564136589)
            ·
              refine ⟨61240673689452018961551221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163308463171872050564136589 61240673689452018961551221)
              ·
                refine ⟨5741313158386126777645427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61240673689452018961551221 5741313158386126777645427)
                ·
                  refine ⟨8611969737579190166468141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5741313158386126777645427 8611969737579190166468141)
                  ·
                    refine ⟨3229488651592196312425553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8611969737579190166468141 3229488651592196312425553)
                    ·
                      refine ⟨2422116488694147234319165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229488651592196312425553 2422116488694147234319165)
                      ·
                        rfl

theorem cell23_4717055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_4717055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717055 prefixEnd_4717055 := by exact prefixLift 4717055
  have htrace : WordTrace (prefixWord ++ tailWord_4717055) baseStart_4717055 baseEnd_4717055 := by
    simpa [prefixWord, tailWord_4717055, baseEnd_4717055] using wordTrace_append hprefix tailTrace_4717055
  have hstable : (prefixWord ++ tailWord_4717055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717055).length < 2 ^ (prefixWord ++ tailWord_4717055).sum := by decide
  have hdescent : baseEnd_4717055 < baseStart_4717055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717061 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_4717061 : Nat := 118140960795 + 4717061 * 2 ^ 59
def prefixEnd_4717061 : Nat := 4983230072969 + 3 ^ 40 * 4717061 * 2
def baseEnd_4717061 : Nat := 807373189859358070281379

theorem tailTrace_4717061 : CollatzResearch.WordTrace tailWord_4717061 prefixEnd_4717061 807373189859358070281379 := by
  unfold tailWord_4717061
  simp only [CollatzResearch.WordTrace]
  refine ⟨172045348763901081726031037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114696899175934054484020691 172045348763901081726031037)
  ·
    refine ⟨64517005786462905647261639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172045348763901081726031037 64517005786462905647261639)
    ·
      refine ⟨96775508679694358470892459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64517005786462905647261639 96775508679694358470892459)
      ·
        refine ⟨145163263019541537706338689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96775508679694358470892459 145163263019541537706338689)
        ·
          refine ⟨108872447264656153279754017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145163263019541537706338689 108872447264656153279754017)
          ·
            refine ⟨81654335448492114959815513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108872447264656153279754017 81654335448492114959815513)
            ·
              refine ⟨61240751586369086219861635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81654335448492114959815513 61240751586369086219861635)
              ·
                refine ⟨91861127379553629329792453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61240751586369086219861635 91861127379553629329792453)
                ·
                  refine ⟨17223961383666305499336085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91861127379553629329792453 17223961383666305499336085)
                  ·
                    refine ⟨807373189859358070281379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17223961383666305499336085 807373189859358070281379)
                    ·
                      rfl

theorem cell23_4717061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_4717061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717061 prefixEnd_4717061 := by exact prefixLift 4717061
  have htrace : WordTrace (prefixWord ++ tailWord_4717061) baseStart_4717061 baseEnd_4717061 := by
    simpa [prefixWord, tailWord_4717061, baseEnd_4717061] using wordTrace_append hprefix tailTrace_4717061
  have hstable : (prefixWord ++ tailWord_4717061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717061).length < 2 ^ (prefixWord ++ tailWord_4717061).sum := by decide
  have hdescent : baseEnd_4717061 < baseStart_4717061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717071 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_4717071 : Nat := 118140960795 + 4717071 * 2 ^ 59
def prefixEnd_4717071 : Nat := 4983230072969 + 3 ^ 40 * 4717071 * 2
def baseEnd_4717071 : Nat := 2422124704384619171719091

theorem tailTrace_4717071 : CollatzResearch.WordTrace tailWord_4717071 prefixEnd_4717071 2422124704384619171719091 := by
  unfold tailWord_4717071
  simp only [CollatzResearch.WordTrace]
  refine ⟨172045713493864853433895067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114697142329243235622596711 172045713493864853433895067)
  ·
    refine ⟨258068570240797280150842601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172045713493864853433895067 258068570240797280150842601)
    ·
      refine ⟨193551427680597960113131951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258068570240797280150842601 193551427680597960113131951)
      ·
        refine ⟨290327141520896940169697927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193551427680597960113131951 290327141520896940169697927)
        ·
          refine ⟨435490712281345410254546891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290327141520896940169697927 435490712281345410254546891)
          ·
            refine ⟨653236068422018115381820337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435490712281345410254546891 653236068422018115381820337)
            ·
              refine ⟨489927051316513586536365253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653236068422018115381820337 489927051316513586536365253)
              ·
                refine ⟨91861322121846297475568485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489927051316513586536365253 91861322121846297475568485)
                ·
                  refine ⟨17223997897846180776669091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91861322121846297475568485 17223997897846180776669091)
                  ·
                    refine ⟨25835996846769271165003637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17223997897846180776669091 25835996846769271165003637)
                    ·
                      refine ⟨2422124704384619171719091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25835996846769271165003637 2422124704384619171719091)
                      ·
                        rfl

theorem cell23_4717071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_4717071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717071 prefixEnd_4717071 := by exact prefixLift 4717071
  have htrace : WordTrace (prefixWord ++ tailWord_4717071) baseStart_4717071 baseEnd_4717071 := by
    simpa [prefixWord, tailWord_4717071, baseEnd_4717071] using wordTrace_append hprefix tailTrace_4717071
  have hstable : (prefixWord ++ tailWord_4717071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717071).length < 2 ^ (prefixWord ++ tailWord_4717071).sum := by decide
  have hdescent : baseEnd_4717071 < baseStart_4717071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717079 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4717079 : Nat := 118140960795 + 4717079 * 2 ^ 59
def prefixEnd_4717079 : Nat := 4983230072969 + 3 ^ 40 * 4717079 * 2
def baseEnd_4717079 : Nat := 2422128812229855140419055

theorem tailTrace_4717079 : CollatzResearch.WordTrace tailWord_4717079 prefixEnd_4717079 2422128812229855140419055 := by
  unfold tailWord_4717079
  simp only [CollatzResearch.WordTrace]
  refine ⟨172046005277835870800186291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114697336851890580533457527 172046005277835870800186291)
  ·
    refine ⟨258069007916753806200279437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172046005277835870800186291 258069007916753806200279437)
    ·
      refine ⟨96775877968782677325104789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258069007916753806200279437 96775877968782677325104789)
      ·
        refine ⟨4536369279786687999614287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96775877968782677325104789 4536369279786687999614287)
        ·
          refine ⟨6804553919680031999421431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4536369279786687999614287 6804553919680031999421431)
          ·
            refine ⟨10206830879520047999132147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804553919680031999421431 10206830879520047999132147)
            ·
              refine ⟨15310246319280071998698221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10206830879520047999132147 15310246319280071998698221)
              ·
                refine ⟨5741342369730026999511833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15310246319280071998698221 5741342369730026999511833)
                ·
                  refine ⟨4306006777297520249633875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5741342369730026999511833 4306006777297520249633875)
                  ·
                    refine ⟨6459010165946280374450813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4306006777297520249633875 6459010165946280374450813)
                    ·
                      refine ⟨2422128812229855140419055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6459010165946280374450813 2422128812229855140419055)
                      ·
                        rfl

theorem cell23_4717079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4717079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717079 prefixEnd_4717079 := by exact prefixLift 4717079
  have htrace : WordTrace (prefixWord ++ tailWord_4717079) baseStart_4717079 baseEnd_4717079 := by
    simpa [prefixWord, tailWord_4717079, baseEnd_4717079] using wordTrace_append hprefix tailTrace_4717079
  have hstable : (prefixWord ++ tailWord_4717079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717079).length < 2 ^ (prefixWord ++ tailWord_4717079).sum := by decide
  have hdescent : baseEnd_4717079 < baseStart_4717079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717125 : List Nat := [1, 3, 1, 1, 1, 6, 1, 4, 5]
def baseStart_4717125 : Nat := 118140960795 + 4717125 * 2 ^ 59
def prefixEnd_4717125 : Nat := 4983230072969 + 3 ^ 40 * 4717125 * 2
def baseEnd_4717125 : Nat := 269128048037773551160427

theorem tailTrace_4717125 : CollatzResearch.WordTrace tailWord_4717125 prefixEnd_4717125 269128048037773551160427 := by
  unfold tailWord_4717125
  simp only [CollatzResearch.WordTrace]
  refine ⟨172047683035669220656360829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114698455357112813770907219 172047683035669220656360829)
  ·
    refine ⟨64517881138375957746135311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172047683035669220656360829 64517881138375957746135311)
    ·
      refine ⟨96776821707563936619202967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64517881138375957746135311 96776821707563936619202967)
      ·
        refine ⟨145165232561345904928804451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96776821707563936619202967 145165232561345904928804451)
        ·
          refine ⟨217747848842018857393206677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145165232561345904928804451 217747848842018857393206677)
          ·
            refine ⟨10206930414469633940306563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 217747848842018857393206677 10206930414469633940306563)
            ·
              refine ⟨15310395621704450910459845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10206930414469633940306563 15310395621704450910459845)
              ·
                refine ⟨2870699179069584545711221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15310395621704450910459845 2870699179069584545711221)
                ·
                  refine ⟨269128048037773551160427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2870699179069584545711221 269128048037773551160427)
                  ·
                    rfl

theorem cell23_4717125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_4717125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717125 prefixEnd_4717125 := by exact prefixLift 4717125
  have htrace : WordTrace (prefixWord ++ tailWord_4717125) baseStart_4717125 baseEnd_4717125 := by
    simpa [prefixWord, tailWord_4717125, baseEnd_4717125] using wordTrace_append hprefix tailTrace_4717125
  have hstable : (prefixWord ++ tailWord_4717125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717125).length < 2 ^ (prefixWord ++ tailWord_4717125).sum := by decide
  have hdescent : baseEnd_4717125 < baseStart_4717125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717138 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_4717138 : Nat := 118140960795 + 4717138 * 2 ^ 59
def prefixEnd_4717138 : Nat := 4983230072969 + 3 ^ 40 * 4717138 * 2
def baseEnd_4717138 : Nat := 807386369196156803193761

theorem tailTrace_4717138 : CollatzResearch.WordTrace tailWord_4717138 prefixEnd_4717138 807386369196156803193761 := by
  unfold tailWord_4717138
  simp only [CollatzResearch.WordTrace]
  refine ⟨43012039296155530969146017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114698771456414749251056045 43012039296155530969146017)
  ·
    refine ⟨32259029472116648226859513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43012039296155530969146017 32259029472116648226859513)
    ·
      refine ⟨24194272104087486170144635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32259029472116648226859513 24194272104087486170144635)
      ·
        refine ⟨36291408156131229255216953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24194272104087486170144635 36291408156131229255216953)
        ·
          refine ⟨27218556117098421941412715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36291408156131229255216953 27218556117098421941412715)
          ·
            refine ⟨40827834175647632912119073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27218556117098421941412715 40827834175647632912119073)
            ·
              refine ⟨30620875631735724684089305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40827834175647632912119073 30620875631735724684089305)
              ·
                refine ⟨22965656723801793513066979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30620875631735724684089305 22965656723801793513066979)
                ·
                  refine ⟨34448485085702690269600469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22965656723801793513066979 34448485085702690269600469)
                  ·
                    refine ⟨807386369196156803193761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34448485085702690269600469 807386369196156803193761)
                    ·
                      rfl

theorem cell23_4717138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_4717138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717138 prefixEnd_4717138 := by exact prefixLift 4717138
  have htrace : WordTrace (prefixWord ++ tailWord_4717138) baseStart_4717138 baseEnd_4717138 := by
    simpa [prefixWord, tailWord_4717138, baseEnd_4717138] using wordTrace_append hprefix tailTrace_4717138
  have hstable : (prefixWord ++ tailWord_4717138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717138).length < 2 ^ (prefixWord ++ tailWord_4717138).sum := by decide
  have hdescent : baseEnd_4717138 < baseStart_4717138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717175 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 2, 4, 2]
def baseStart_4717175 : Nat := 118140960795 + 4717175 * 2 ^ 59
def prefixEnd_4717175 : Nat := 4983230072969 + 3 ^ 40 * 4717175 * 2
def baseEnd_4717175 : Nat := 2422178106372686764818613

theorem tailTrace_4717175 : CollatzResearch.WordTrace tailWord_4717175 prefixEnd_4717175 2422178106372686764818613 := by
  unfold tailWord_4717175
  simp only [CollatzResearch.WordTrace]
  refine ⟨172049506685488079195680979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114699671123658719463787319 172049506685488079195680979)
  ·
    refine ⟨258074260028232118793521469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172049506685488079195680979 258074260028232118793521469)
    ·
      refine ⟨96777847510587044547570551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258074260028232118793521469 96777847510587044547570551)
      ·
        refine ⟨145166771265880566821355827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96777847510587044547570551 145166771265880566821355827)
        ·
          refine ⟨217750156898820850232033741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145166771265880566821355827 217750156898820850232033741)
          ·
            refine ⟨81656308837057818837012653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217750156898820850232033741 81656308837057818837012653)
            ·
              refine ⟨30621115813896682063879745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81656308837057818837012653 30621115813896682063879745)
              ·
                refine ⟨22965836860422511547909809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30621115813896682063879745 22965836860422511547909809)
                ·
                  refine ⟨17224377645316883660932357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22965836860422511547909809 17224377645316883660932357)
                  ·
                    refine ⟨3229570808496915686424817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17224377645316883660932357 3229570808496915686424817)
                    ·
                      refine ⟨2422178106372686764818613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229570808496915686424817 2422178106372686764818613)
                      ·
                        rfl

theorem cell23_4717175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_4717175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717175 prefixEnd_4717175 := by exact prefixLift 4717175
  have htrace : WordTrace (prefixWord ++ tailWord_4717175) baseStart_4717175 baseEnd_4717175 := by
    simpa [prefixWord, tailWord_4717175, baseEnd_4717175] using wordTrace_append hprefix tailTrace_4717175
  have hstable : (prefixWord ++ tailWord_4717175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717175).length < 2 ^ (prefixWord ++ tailWord_4717175).sum := by decide
  have hdescent : baseEnd_4717175 < baseStart_4717175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717202 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_4717202 : Nat := 118140960795 + 4717202 * 2 ^ 59
def prefixEnd_4717202 : Nat := 4983230072969 + 3 ^ 40 * 4717202 * 2
def baseEnd_4717202 : Nat := 807397323450119386393663

theorem tailTrace_4717202 : CollatzResearch.WordTrace tailWord_4717202 prefixEnd_4717202 807397323450119386393663 := by
  unfold tailWord_4717202
  simp only [CollatzResearch.WordTrace]
  refine ⟨43012622864097565701728465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114700327637593508537942573 43012622864097565701728465)
  ·
    refine ⟨32259467148073174276296349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43012622864097565701728465 32259467148073174276296349)
    ·
      refine ⟨12097300180527440353611131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32259467148073174276296349 12097300180527440353611131)
      ·
        refine ⟨18145950270791160530416697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12097300180527440353611131 18145950270791160530416697)
        ·
          refine ⟨13609462703093370397812523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18145950270791160530416697 13609462703093370397812523)
          ·
            refine ⟨20414194054640055596718785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13609462703093370397812523 20414194054640055596718785)
            ·
              refine ⟨15310645540980041697539089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20414194054640055596718785 15310645540980041697539089)
              ·
                refine ⟨11482984155735031273154317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15310645540980041697539089 11482984155735031273154317)
                ·
                  refine ⟨4306119058400636727432869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11482984155735031273154317 4306119058400636727432869)
                  ·
                    refine ⟨807397323450119386393663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4306119058400636727432869 807397323450119386393663)
                    ·
                      rfl

theorem cell23_4717202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_4717202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717202 prefixEnd_4717202 := by exact prefixLift 4717202
  have htrace : WordTrace (prefixWord ++ tailWord_4717202) baseStart_4717202 baseEnd_4717202 := by
    simpa [prefixWord, tailWord_4717202, baseEnd_4717202] using wordTrace_append hprefix tailTrace_4717202
  have hstable : (prefixWord ++ tailWord_4717202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717202).length < 2 ^ (prefixWord ++ tailWord_4717202).sum := by decide
  have hdescent : baseEnd_4717202 < baseStart_4717202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717225 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 3]
def baseStart_4717225 : Nat := 118140960795 + 4717225 * 2 ^ 59
def prefixEnd_4717225 : Nat := 4983230072969 + 3 ^ 40 * 4717225 * 2
def baseEnd_4717225 : Nat := 2422203780405411569193383

theorem tailTrace_4717225 : CollatzResearch.WordTrace tailWord_4717225 prefixEnd_4717225 2422203780405411569193383 := by
  unfold tailWord_4717225
  simp only [CollatzResearch.WordTrace]
  refine ⟨172051330335306937735001129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114700886890204625156667419 172051330335306937735001129)
  ·
    refine ⟨129038497751480203301250847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172051330335306937735001129 129038497751480203301250847)
    ·
      refine ⟨193557746627220304951876271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129038497751480203301250847 193557746627220304951876271)
      ·
        refine ⟨290336619940830457427814407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193557746627220304951876271 290336619940830457427814407)
        ·
          refine ⟨435504929911245686141721611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290336619940830457427814407 435504929911245686141721611)
          ·
            refine ⟨653257394866868529212582417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435504929911245686141721611 653257394866868529212582417)
            ·
              refine ⟨489943046150151396909436813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653257394866868529212582417 489943046150151396909436813)
              ·
                refine ⟨183728642306306773841038805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 489943046150151396909436813 183728642306306773841038805)
                ·
                  refine ⟨4306140054054065011899347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 183728642306306773841038805 4306140054054065011899347)
                  ·
                    refine ⟨6459210081081097517849021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4306140054054065011899347 6459210081081097517849021)
                    ·
                      refine ⟨2422203780405411569193383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6459210081081097517849021 2422203780405411569193383)
                      ·
                        rfl

theorem cell23_4717225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 3].length) (baseStart_4717225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717225 prefixEnd_4717225 := by exact prefixLift 4717225
  have htrace : WordTrace (prefixWord ++ tailWord_4717225) baseStart_4717225 baseEnd_4717225 := by
    simpa [prefixWord, tailWord_4717225, baseEnd_4717225] using wordTrace_append hprefix tailTrace_4717225
  have hstable : (prefixWord ++ tailWord_4717225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717225).length < 2 ^ (prefixWord ++ tailWord_4717225).sum := by decide
  have hdescent : baseEnd_4717225 < baseStart_4717225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717249 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 6]
def baseStart_4717249 : Nat := 118140960795 + 4717249 * 2 ^ 59
def prefixEnd_4717249 : Nat := 4983230072969 + 3 ^ 40 * 4717249 * 2
def baseEnd_4717249 : Nat := 269135122660124386143697

theorem tailTrace_4717249 : CollatzResearch.WordTrace tailWord_4717249 prefixEnd_4717249 269135122660124386143697 := by
  unfold tailWord_4717249
  simp only [CollatzResearch.WordTrace]
  refine ⟨172052205687219989833874801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114701470458146659889249867 172052205687219989833874801)
  ·
    refine ⟨129039154265414992375406101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172052205687219989833874801 129039154265414992375406101)
    ·
      refine ⟨6048710356191327767597161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129039154265414992375406101 6048710356191327767597161)
      ·
        refine ⟨4536532767143495825697871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6048710356191327767597161 4536532767143495825697871)
        ·
          refine ⟨6804799150715243738546807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4536532767143495825697871 6804799150715243738546807)
          ·
            refine ⟨10207198726072865607820211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804799150715243738546807 10207198726072865607820211)
            ·
              refine ⟨15310798089109298411730317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10207198726072865607820211 15310798089109298411730317)
              ·
                refine ⟨5741549283415986904398869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15310798089109298411730317 5741549283415986904398869)
                ·
                  refine ⟨269135122660124386143697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5741549283415986904398869 269135122660124386143697)
                  ·
                    rfl

theorem cell23_4717249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 6].length) (baseStart_4717249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717249 prefixEnd_4717249 := by exact prefixLift 4717249
  have htrace : WordTrace (prefixWord ++ tailWord_4717249) baseStart_4717249 baseEnd_4717249 := by
    simpa [prefixWord, tailWord_4717249, baseEnd_4717249] using wordTrace_append hprefix tailTrace_4717249
  have hstable : (prefixWord ++ tailWord_4717249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717249).length < 2 ^ (prefixWord ++ tailWord_4717249).sum := by decide
  have hdescent : baseEnd_4717249 < baseStart_4717249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717262 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_4717262 : Nat := 118140960795 + 4717262 * 2 ^ 59
def prefixEnd_4717262 : Nat := 4983230072969 + 3 ^ 40 * 4717262 * 2
def baseEnd_4717262 : Nat := 807407593063209308143571

theorem tailTrace_4717262 : CollatzResearch.WordTrace tailWord_4717262 prefixEnd_4717262 807407593063209308143571 := by
  unfold tailWord_4717262
  simp only [CollatzResearch.WordTrace]
  refine ⟨21506584979521611631762255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114701786557448595369398693 21506584979521611631762255)
  ·
    refine ⟨32259877469282417447643383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21506584979521611631762255 32259877469282417447643383)
    ·
      refine ⟨48389816203923626171465075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32259877469282417447643383 48389816203923626171465075)
      ·
        refine ⟨72584724305885439257197613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48389816203923626171465075 72584724305885439257197613)
        ·
          refine ⟨27219271614707039721449105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72584724305885439257197613 27219271614707039721449105)
          ·
            refine ⟨20414453711030279791086829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27219271614707039721449105 20414453711030279791086829)
            ·
              refine ⟨7655420141636354921657561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20414453711030279791086829 7655420141636354921657561)
              ·
                refine ⟨5741565106227266191243171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7655420141636354921657561 5741565106227266191243171)
                ·
                  refine ⟨8612347659340899286864757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5741565106227266191243171 8612347659340899286864757)
                  ·
                    refine ⟨807407593063209308143571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8612347659340899286864757 807407593063209308143571)
                    ·
                      rfl

theorem cell23_4717262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_4717262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717262 prefixEnd_4717262 := by exact prefixLift 4717262
  have htrace : WordTrace (prefixWord ++ tailWord_4717262) baseStart_4717262 baseEnd_4717262 := by
    simpa [prefixWord, tailWord_4717262, baseEnd_4717262] using wordTrace_append hprefix tailTrace_4717262
  have hstable : (prefixWord ++ tailWord_4717262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717262).length < 2 ^ (prefixWord ++ tailWord_4717262).sum := by decide
  have hdescent : baseEnd_4717262 < baseStart_4717262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717265 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_4717265 : Nat := 118140960795 + 4717265 * 2 ^ 59
def prefixEnd_4717265 : Nat := 4983230072969 + 3 ^ 40 * 4717265 * 2
def baseEnd_4717265 : Nat := 2422224319631591412693199

theorem tailTrace_4717265 : CollatzResearch.WordTrace tailWord_4717265 prefixEnd_4717265 2422224319631591412693199 := by
  unfold tailWord_4717265
  simp only [CollatzResearch.WordTrace]
  refine ⟨172052789255162024566457249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114701859503441349710971499 172052789255162024566457249)
  ·
    refine ⟨129039591941371518424842937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172052789255162024566457249 129039591941371518424842937)
    ·
      refine ⟨96779693956028638818632203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129039591941371518424842937 96779693956028638818632203)
      ·
        refine ⟨145169540934042958227948305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96779693956028638818632203 145169540934042958227948305)
        ·
          refine ⟨108877155700532218670961229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145169540934042958227948305 108877155700532218670961229)
          ·
            refine ⟨40828933387699582001610461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108877155700532218670961229 40828933387699582001610461)
            ·
              refine ⟨15310850020387343250603923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40828933387699582001610461 15310850020387343250603923)
              ·
                refine ⟨22966275030581014875905885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15310850020387343250603923 22966275030581014875905885)
                ·
                  refine ⟨8612353136467880578464707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22966275030581014875905885 8612353136467880578464707)
                  ·
                    refine ⟨12918529704701820867697061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8612353136467880578464707 12918529704701820867697061)
                    ·
                      refine ⟨2422224319631591412693199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12918529704701820867697061 2422224319631591412693199)
                      ·
                        rfl

theorem cell23_4717265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_4717265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717265 prefixEnd_4717265 := by exact prefixLift 4717265
  have htrace : WordTrace (prefixWord ++ tailWord_4717265) baseStart_4717265 baseEnd_4717265 := by
    simpa [prefixWord, tailWord_4717265, baseEnd_4717265] using wordTrace_append hprefix tailTrace_4717265
  have hstable : (prefixWord ++ tailWord_4717265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717265).length < 2 ^ (prefixWord ++ tailWord_4717265).sum := by decide
  have hdescent : baseEnd_4717265 < baseStart_4717265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717288 : List Nat := [2, 1, 4, 1, 15]
def baseStart_4717288 : Nat := 118140960795 + 4717288 * 2 ^ 59
def prefixEnd_4717288 : Nat := 4983230072969 + 3 ^ 40 * 4717288 * 2
def baseEnd_4717288 : Nat := 3322683305468648590817

theorem tailTrace_4717288 : CollatzResearch.WordTrace tailWord_4717288 prefixEnd_4717288 3322683305468648590817 := by
  unfold tailWord_4717288
  simp only [CollatzResearch.WordTrace]
  refine ⟨86026814067039349747272259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114702418756052466329696345 86026814067039349747272259)
  ·
    refine ⟨129040221100559024620908389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86026814067039349747272259 129040221100559024620908389)
    ·
      refine ⟨24195041456354817116420323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129040221100559024620908389 24195041456354817116420323)
      ·
        refine ⟨36292562184532225674630485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24195041456354817116420323 36292562184532225674630485)
        ·
          refine ⟨3322683305468648590817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 36292562184532225674630485 3322683305468648590817)
          ·
            rfl

theorem cell23_4717288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 15].length) (baseStart_4717288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717288 prefixEnd_4717288 := by exact prefixLift 4717288
  have htrace : WordTrace (prefixWord ++ tailWord_4717288) baseStart_4717288 baseEnd_4717288 := by
    simpa [prefixWord, tailWord_4717288, baseEnd_4717288] using wordTrace_append hprefix tailTrace_4717288
  have hstable : (prefixWord ++ tailWord_4717288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717288).length < 2 ^ (prefixWord ++ tailWord_4717288).sum := by decide
  have hdescent : baseEnd_4717288 < baseStart_4717288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717302 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_4717302 : Nat := 118140960795 + 4717302 * 2 ^ 59
def prefixEnd_4717302 : Nat := 4983230072969 + 3 ^ 40 * 4717302 * 2
def baseEnd_4717302 : Nat := 2422243318415807767930529

theorem tailTrace_4717302 : CollatzResearch.WordTrace tailWord_4717302 prefixEnd_4717302 2422243318415807767930529 := by
  unfold tailWord_4717302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753383672251748742847135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114702759170685319923702773 10753383672251748742847135)
  ·
    refine ⟨16130075508377623114270703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10753383672251748742847135 16130075508377623114270703)
    ·
      refine ⟨24195113262566434671406055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16130075508377623114270703 24195113262566434671406055)
      ·
        refine ⟨36292669893849652007109083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24195113262566434671406055 36292669893849652007109083)
        ·
          refine ⟨54439004840774478010663625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36292669893849652007109083 54439004840774478010663625)
          ·
            refine ⟨40829253630580858507997719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54439004840774478010663625 40829253630580858507997719)
            ·
              refine ⟨61243880445871287761996579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40829253630580858507997719 61243880445871287761996579)
              ·
                refine ⟨91865820668806931642994869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61243880445871287761996579 91865820668806931642994869)
                ·
                  refine ⟨8612420687700649841530769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91865820668806931642994869 8612420687700649841530769)
                  ·
                    refine ⟨6459315515775487381148077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8612420687700649841530769 6459315515775487381148077)
                    ·
                      refine ⟨2422243318415807767930529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6459315515775487381148077 2422243318415807767930529)
                      ·
                        rfl

theorem cell23_4717302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_4717302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717302 prefixEnd_4717302 := by exact prefixLift 4717302
  have htrace : WordTrace (prefixWord ++ tailWord_4717302) baseStart_4717302 baseEnd_4717302 := by
    simpa [prefixWord, tailWord_4717302, baseEnd_4717302] using wordTrace_append hprefix tailTrace_4717302
  have hstable : (prefixWord ++ tailWord_4717302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717302).length < 2 ^ (prefixWord ++ tailWord_4717302).sum := by decide
  have hdescent : baseEnd_4717302 < baseStart_4717302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717328 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_4717328 : Nat := 118140960795 + 4717328 * 2 ^ 59
def prefixEnd_4717328 : Nat := 4983230072969 + 3 ^ 40 * 4717328 * 2
def baseEnd_4717328 : Nat := 2422256668912824666205409

theorem tailTrace_4717328 : CollatzResearch.WordTrace tailWord_4717328 prefixEnd_4717328 2422256668912824666205409 := by
  unfold tailWord_4717328
  simp only [CollatzResearch.WordTrace]
  refine ⟨86027543526966893163000319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114703391369289190884000425 86027543526966893163000319)
  ·
    refine ⟨129041315290450339744500479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86027543526966893163000319 129041315290450339744500479)
    ·
      refine ⟨193561972935675509616750719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129041315290450339744500479 193561972935675509616750719)
      ·
        refine ⟨290342959403513264425126079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193561972935675509616750719 290342959403513264425126079)
        ·
          refine ⟨435514439105269896637689119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290342959403513264425126079 435514439105269896637689119)
          ·
            refine ⟨653271658657904844956533679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435514439105269896637689119 653271658657904844956533679)
            ·
              refine ⟨979907487986857267434800519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653271658657904844956533679 979907487986857267434800519)
              ·
                refine ⟨1469861231980285901152200779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979907487986857267434800519 1469861231980285901152200779)
                ·
                  refine ⟨2204791847970428851728301169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469861231980285901152200779 2204791847970428851728301169)
                  ·
                    refine ⟨1653593885977821638796225877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2204791847970428851728301169 1653593885977821638796225877)
                    ·
                      refine ⟨2422256668912824666205409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1653593885977821638796225877 2422256668912824666205409)
                      ·
                        rfl

theorem cell23_4717328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_4717328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717328 prefixEnd_4717328 := by exact prefixLift 4717328
  have htrace : WordTrace (prefixWord ++ tailWord_4717328) baseStart_4717328 baseEnd_4717328 := by
    simpa [prefixWord, tailWord_4717328, baseEnd_4717328] using wordTrace_append hprefix tailTrace_4717328
  have hstable : (prefixWord ++ tailWord_4717328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717328).length < 2 ^ (prefixWord ++ tailWord_4717328).sum := by decide
  have hdescent : baseEnd_4717328 < baseStart_4717328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717412 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 7]
def baseStart_4717412 : Nat := 118140960795 + 4717412 * 2 ^ 59
def prefixEnd_4717412 : Nat := 4983230072969 + 3 ^ 40 * 4717412 * 2
def baseEnd_4717412 : Nat := 269144422365311370839447

theorem tailTrace_4717412 : CollatzResearch.WordTrace tailWord_4717412 prefixEnd_4717412 269144422365311370839447 := by
  unfold tailWord_4717412
  simp only [CollatzResearch.WordTrace]
  refine ⟨86029075392814734336029245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114705433857086312448038993 86029075392814734336029245)
  ·
    refine ⟨32260903272305525376010967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86029075392814734336029245 32260903272305525376010967)
    ·
      refine ⟨48391354908458288064016451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32260903272305525376010967 48391354908458288064016451)
      ·
        refine ⟨72587032362687432096024677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48391354908458288064016451 72587032362687432096024677)
        ·
          refine ⟨13610068568003893518004627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72587032362687432096024677 13610068568003893518004627)
          ·
            refine ⟨20415102852005840277006941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13610068568003893518004627 20415102852005840277006941)
            ·
              refine ⟨7655663569502190103877603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20415102852005840277006941 7655663569502190103877603)
              ·
                refine ⟨11483495354253285155816405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7655663569502190103877603 11483495354253285155816405)
                ·
                  refine ⟨269144422365311370839447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11483495354253285155816405 269144422365311370839447)
                  ·
                    rfl

theorem cell23_4717412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_4717412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717412 prefixEnd_4717412 := by exact prefixLift 4717412
  have htrace : WordTrace (prefixWord ++ tailWord_4717412) baseStart_4717412 baseEnd_4717412 := by
    simpa [prefixWord, tailWord_4717412, baseEnd_4717412] using wordTrace_append hprefix tailTrace_4717412
  have hstable : (prefixWord ++ tailWord_4717412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717412).length < 2 ^ (prefixWord ++ tailWord_4717412).sum := by decide
  have hdescent : baseEnd_4717412 < baseStart_4717412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717432 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 4, 5, 2]
def baseStart_4717432 : Nat := 118140960795 + 4717432 * 2 ^ 59
def prefixEnd_4717432 : Nat := 4983230072969 + 3 ^ 40 * 4717432 * 2
def baseEnd_4717432 : Nat := 2422310070900892259304931

theorem tailTrace_4717432 : CollatzResearch.WordTrace tailWord_4717432 prefixEnd_4717432 2422310070900892259304931 := by
  unfold tailWord_4717432
  simp only [CollatzResearch.WordTrace]
  refine ⟨86029440122778506043893275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114705920163704674725191033 86029440122778506043893275)
  ·
    refine ⟨129044160184167759065839913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86029440122778506043893275 129044160184167759065839913)
    ·
      refine ⟨96783120138125819299379935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129044160184167759065839913 96783120138125819299379935)
      ·
        refine ⟨145174680207188728949069903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96783120138125819299379935 145174680207188728949069903)
        ·
          refine ⟨217762020310783093423604855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145174680207188728949069903 217762020310783093423604855)
          ·
            refine ⟨326643030466174640135407283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217762020310783093423604855 326643030466174640135407283)
            ·
              refine ⟨489964545699261960203110925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326643030466174640135407283 489964545699261960203110925)
              ·
                refine ⟨183736704637223235076166597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 489964545699261960203110925 183736704637223235076166597)
                ·
                  refine ⟨34450632119479356576781237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183736704637223235076166597 34450632119479356576781237)
                  ·
                    refine ⟨3229746761201189679073241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34450632119479356576781237 3229746761201189679073241)
                    ·
                      refine ⟨2422310070900892259304931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229746761201189679073241 2422310070900892259304931)
                      ·
                        rfl

theorem cell23_4717432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_4717432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717432 prefixEnd_4717432 := by exact prefixLift 4717432
  have htrace : WordTrace (prefixWord ++ tailWord_4717432) baseStart_4717432 baseEnd_4717432 := by
    simpa [prefixWord, tailWord_4717432, baseEnd_4717432] using wordTrace_append hprefix tailTrace_4717432
  have hstable : (prefixWord ++ tailWord_4717432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717432).length < 2 ^ (prefixWord ++ tailWord_4717432).sum := by decide
  have hdescent : baseEnd_4717432 < baseStart_4717432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717465 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_4717465 : Nat := 118140960795 + 4717465 * 2 ^ 59
def prefixEnd_4717465 : Nat := 4983230072969 + 3 ^ 40 * 4717465 * 2
def baseEnd_4717465 : Nat := 2422327015762490630192279

theorem tailTrace_4717465 : CollatzResearch.WordTrace tailWord_4717465 prefixEnd_4717465 2422327015762490630192279 := by
  unfold tailWord_4717465
  simp only [CollatzResearch.WordTrace]
  refine ⟨172060083854437458723737849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114706722569624972482491899 172060083854437458723737849)
  ·
    refine ⟨129045062890828094042803387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172060083854437458723737849 129045062890828094042803387)
    ·
      refine ⟨193567594336242141064205081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129045062890828094042803387 193567594336242141064205081)
      ·
        refine ⟨145175695752181605798153811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193567594336242141064205081 145175695752181605798153811)
        ·
          refine ⟨217763543628272408697230717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145175695752181605798153811 217763543628272408697230717)
          ·
            refine ⟨81661328860602153261461519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217763543628272408697230717 81661328860602153261461519)
            ·
              refine ⟨122491993290903229892192279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81661328860602153261461519 122491993290903229892192279)
              ·
                refine ⟨183737989936354844838288419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122491993290903229892192279 183737989936354844838288419)
                ·
                  refine ⟨275606984904532267257432629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183737989936354844838288419 275606984904532267257432629)
                  ·
                    refine ⟨25838154834799900055384309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 275606984904532267257432629 25838154834799900055384309)
                    ·
                      refine ⟨2422327015762490630192279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25838154834799900055384309 2422327015762490630192279)
                      ·
                        rfl

theorem cell23_4717465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_4717465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717465 prefixEnd_4717465 := by exact prefixLift 4717465
  have htrace : WordTrace (prefixWord ++ tailWord_4717465) baseStart_4717465 baseEnd_4717465 := by
    simpa [prefixWord, tailWord_4717465, baseEnd_4717465] using wordTrace_append hprefix tailTrace_4717465
  have hstable : (prefixWord ++ tailWord_4717465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717465).length < 2 ^ (prefixWord ++ tailWord_4717465).sum := by decide
  have hdescent : baseEnd_4717465 < baseStart_4717465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717502 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_4717502 : Nat := 118140960795 + 4717502 * 2 ^ 59
def prefixEnd_4717502 : Nat := 4983230072969 + 3 ^ 40 * 4717502 * 2
def baseEnd_4717502 : Nat := 269149557171856331714401

theorem tailTrace_4717502 : CollatzResearch.WordTrace tailWord_4717502 prefixEnd_4717502 269149557171856331714401 := by
  unfold tailWord_4717502
  simp only [CollatzResearch.WordTrace]
  refine ⟨21507679169412926755354345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114707622236868942695223173 21507679169412926755354345)
  ·
    refine ⟨16130759377059695066515759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21507679169412926755354345 16130759377059695066515759)
    ·
      refine ⟨24196139065589542599773639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16130759377059695066515759 24196139065589542599773639)
      ·
        refine ⟨36294208598384313899660459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24196139065589542599773639 36294208598384313899660459)
        ·
          refine ⟨54441312897576470849490689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36294208598384313899660459 54441312897576470849490689)
          ·
            refine ⟨40830984673182353137118017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54441312897576470849490689 40830984673182353137118017)
            ·
              refine ⟨30623238504886764852838513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40830984673182353137118017 30623238504886764852838513)
              ·
                refine ⟨22967428878665073639628885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30623238504886764852838513 22967428878665073639628885)
                ·
                  refine ⟨269149557171856331714401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22967428878665073639628885 269149557171856331714401)
                  ·
                    rfl

theorem cell23_4717502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_4717502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717502 prefixEnd_4717502 := by exact prefixLift 4717502
  have htrace : WordTrace (prefixWord ++ tailWord_4717502) baseStart_4717502 baseEnd_4717502 := by
    simpa [prefixWord, tailWord_4717502, baseEnd_4717502] using wordTrace_append hprefix tailTrace_4717502
  have hstable : (prefixWord ++ tailWord_4717502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717502).length < 2 ^ (prefixWord ++ tailWord_4717502).sum := by decide
  have hdescent : baseEnd_4717502 < baseStart_4717502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717519 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 6]
def baseStart_4717519 : Nat := 118140960795 + 4717519 * 2 ^ 59
def prefixEnd_4717519 : Nat := 4983230072969 + 3 ^ 40 * 4717519 * 2
def baseEnd_4717519 : Nat := 269150527079759268768559

theorem tailTrace_4717519 : CollatzResearch.WordTrace tailWord_4717519 prefixEnd_4717519 269150527079759268768559 := by
  unfold tailWord_4717519
  simp only [CollatzResearch.WordTrace]
  refine ⟨172062053396241825946203611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114708035597494550630802407 172062053396241825946203611)
  ·
    refine ⟨258093080094362738919305417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172062053396241825946203611 258093080094362738919305417)
    ·
      refine ⟨193569810070772054189479063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258093080094362738919305417 193569810070772054189479063)
      ·
        refine ⟨290354715106158081284218595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193569810070772054189479063 290354715106158081284218595)
        ·
          refine ⟨435532072659237121926327893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290354715106158081284218595 435532072659237121926327893)
          ·
            refine ⟨5103891476475435022574155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 435532072659237121926327893 5103891476475435022574155)
            ·
              refine ⟨7655837214713152533861233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103891476475435022574155 7655837214713152533861233)
              ·
                refine ⟨5741877911034864400395925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7655837214713152533861233 5741877911034864400395925)
                ·
                  refine ⟨269150527079759268768559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5741877911034864400395925 269150527079759268768559)
                  ·
                    rfl

theorem cell23_4717519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 6].length) (baseStart_4717519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717519 prefixEnd_4717519 := by exact prefixLift 4717519
  have htrace : WordTrace (prefixWord ++ tailWord_4717519) baseStart_4717519 baseEnd_4717519 := by
    simpa [prefixWord, tailWord_4717519, baseEnd_4717519] using wordTrace_append hprefix tailTrace_4717519
  have hstable : (prefixWord ++ tailWord_4717519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717519).length < 2 ^ (prefixWord ++ tailWord_4717519).sum := by decide
  have hdescent : baseEnd_4717519 < baseStart_4717519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717539 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 3, 5, 2]
def baseStart_4717539 : Nat := 118140960795 + 4717539 * 2 ^ 59
def prefixEnd_4717539 : Nat := 4983230072969 + 3 ^ 40 * 4717539 * 2
def baseEnd_4717539 : Nat := 2422365013330923340666939

theorem tailTrace_4717539 : CollatzResearch.WordTrace tailWord_4717539 prefixEnd_4717539 2422365013330923340666939 := by
  unfold tailWord_4717539
  simp only [CollatzResearch.WordTrace]
  refine ⟨172062782856169369361931671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114708521904112912907954447 172062782856169369361931671)
  ·
    refine ⟨258094174284254054042897507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172062782856169369361931671 258094174284254054042897507)
    ·
      refine ⟨387141261426381081064346261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258094174284254054042897507 387141261426381081064346261)
      ·
        refine ⟨18147246629361613174891231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 387141261426381081064346261 18147246629361613174891231)
        ·
          refine ⟨27220869944042419762336847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18147246629361613174891231 27220869944042419762336847)
          ·
            refine ⟨40831304916063629643505271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27220869944042419762336847 40831304916063629643505271)
            ·
              refine ⟨61246957374095444465257907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40831304916063629643505271 61246957374095444465257907)
              ·
                refine ⟨91870436061143166697886861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61246957374095444465257907 91870436061143166697886861)
                ·
                  refine ⟨34451413522928687511707573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91870436061143166697886861 34451413522928687511707573)
                  ·
                    refine ⟨3229820017774564454222585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34451413522928687511707573 3229820017774564454222585)
                    ·
                      refine ⟨2422365013330923340666939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229820017774564454222585 2422365013330923340666939)
                      ·
                        rfl

theorem cell23_4717539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_4717539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717539 prefixEnd_4717539 := by exact prefixLift 4717539
  have htrace : WordTrace (prefixWord ++ tailWord_4717539) baseStart_4717539 baseEnd_4717539 := by
    simpa [prefixWord, tailWord_4717539, baseEnd_4717539] using wordTrace_append hprefix tailTrace_4717539
  have hstable : (prefixWord ++ tailWord_4717539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717539).length < 2 ^ (prefixWord ++ tailWord_4717539).sum := by decide
  have hdescent : baseEnd_4717539 < baseStart_4717539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717546 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_4717546 : Nat := 118140960795 + 4717546 * 2 ^ 59
def prefixEnd_4717546 : Nat := 4983230072969 + 3 ^ 40 * 4717546 * 2
def baseEnd_4717546 : Nat := 2422368607695504813279407

theorem tailTrace_4717546 : CollatzResearch.WordTrace tailWord_4717546 prefixEnd_4717546 2422368607695504813279407 := by
  unfold tailWord_4717546
  simp only [CollatzResearch.WordTrace]
  refine ⟨43015759541786002389359123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114708692111429339704957661 43015759541786002389359123)
  ·
    refine ⟨64523639312679003584038685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43015759541786002389359123 64523639312679003584038685)
    ·
      refine ⟨24196364742254626344014507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64523639312679003584038685 24196364742254626344014507)
      ·
        refine ⟨36294547113381939516021761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24196364742254626344014507 36294547113381939516021761)
        ·
          refine ⟨27220910335036454637016321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36294547113381939516021761 27220910335036454637016321)
          ·
            refine ⟨20415682751277340977762241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27220910335036454637016321 20415682751277340977762241)
            ·
              refine ⟨15311762063458005733321681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20415682751277340977762241 15311762063458005733321681)
              ·
                refine ⟨11483821547593504299991261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15311762063458005733321681 11483821547593504299991261)
                ·
                  refine ⟨4306433080347564112496723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11483821547593504299991261 4306433080347564112496723)
                  ·
                    refine ⟨6459649620521346168745085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4306433080347564112496723 6459649620521346168745085)
                    ·
                      refine ⟨2422368607695504813279407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6459649620521346168745085 2422368607695504813279407)
                      ·
                        rfl

theorem cell23_4717546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_4717546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717546 prefixEnd_4717546 := by exact prefixLift 4717546
  have htrace : WordTrace (prefixWord ++ tailWord_4717546) baseStart_4717546 baseEnd_4717546 := by
    simpa [prefixWord, tailWord_4717546, baseEnd_4717546] using wordTrace_append hprefix tailTrace_4717546
  have hstable : (prefixWord ++ tailWord_4717546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717546).length < 2 ^ (prefixWord ++ tailWord_4717546).sum := by decide
  have hdescent : baseEnd_4717546 < baseStart_4717546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717557 : List Nat := [1, 3, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4717557 : Nat := 118140960795 + 4717557 * 2 ^ 59
def prefixEnd_4717557 : Nat := 4983230072969 + 3 ^ 40 * 4717557 * 2
def baseEnd_4717557 : Nat := 807458085327568090080619

theorem tailTrace_4717557 : CollatzResearch.WordTrace tailWord_4717557 prefixEnd_4717557 807458085327568090080619 := by
  unfold tailWord_4717557
  simp only [CollatzResearch.WordTrace]
  refine ⟨172063439370104158436086925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114708959580069438957391283 172063439370104158436086925)
  ·
    refine ⟨64523789763789059413532597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172063439370104158436086925 64523789763789059413532597)
    ·
      refine ⟨6049105290355224320018681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64523789763789059413532597 6049105290355224320018681)
      ·
        refine ⟨4536828967766418240014011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6049105290355224320018681 4536828967766418240014011)
        ·
          refine ⟨6805243451649627360021017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4536828967766418240014011 6805243451649627360021017)
          ·
            refine ⟨5103932588737220520015763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6805243451649627360021017 5103932588737220520015763)
            ·
              refine ⟨7655898883105830780023645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103932588737220520015763 7655898883105830780023645)
              ·
                refine ⟨2870962081164686542508867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7655898883105830780023645 2870962081164686542508867)
                ·
                  refine ⟨4306443121747029813763301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870962081164686542508867 4306443121747029813763301)
                  ·
                    refine ⟨807458085327568090080619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4306443121747029813763301 807458085327568090080619)
                    ·
                      rfl

theorem cell23_4717557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4717557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717557 prefixEnd_4717557 := by exact prefixLift 4717557
  have htrace : WordTrace (prefixWord ++ tailWord_4717557) baseStart_4717557 baseEnd_4717557 := by
    simpa [prefixWord, tailWord_4717557, baseEnd_4717557] using wordTrace_append hprefix tailTrace_4717557
  have hstable : (prefixWord ++ tailWord_4717557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717557).length < 2 ^ (prefixWord ++ tailWord_4717557).sum := by decide
  have hdescent : baseEnd_4717557 < baseStart_4717557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717562 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_4717562 : Nat := 118140960795 + 4717562 * 2 ^ 59
def prefixEnd_4717562 : Nat := 4983230072969 + 3 ^ 40 * 4717562 * 2
def baseEnd_4717562 : Nat := 807458941128658916893111

theorem tailTrace_4717562 : CollatzResearch.WordTrace tailWord_4717562 prefixEnd_4717562 807458941128658916893111 := by
  unfold tailWord_4717562
  simp only [CollatzResearch.WordTrace]
  refine ⟨43015905433771511072504735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114709081156724029526679293 43015905433771511072504735)
  ·
    refine ⟨64523858150657266608757103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43015905433771511072504735 64523858150657266608757103)
    ·
      refine ⟨96785787225985899913135655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64523858150657266608757103 96785787225985899913135655)
      ·
        refine ⟨145178680838978849869703483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96785787225985899913135655 145178680838978849869703483)
        ·
          refine ⟨217768021258468274804555225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145178680838978849869703483 217768021258468274804555225)
          ·
            refine ⟨163326015943851206103416419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217768021258468274804555225 163326015943851206103416419)
            ·
              refine ⟨244989023915776809155124629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163326015943851206103416419 244989023915776809155124629)
              ·
                refine ⟨11483860496052037929146467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 244989023915776809155124629 11483860496052037929146467)
                ·
                  refine ⟨17225790744078056893719701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11483860496052037929146467 17225790744078056893719701)
                  ·
                    refine ⟨807458941128658916893111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17225790744078056893719701 807458941128658916893111)
                    ·
                      rfl

theorem cell23_4717562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_4717562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717562 prefixEnd_4717562 := by exact prefixLift 4717562
  have htrace : WordTrace (prefixWord ++ tailWord_4717562) baseStart_4717562 baseEnd_4717562 := by
    simpa [prefixWord, tailWord_4717562, baseEnd_4717562] using wordTrace_append hprefix tailTrace_4717562
  have hstable : (prefixWord ++ tailWord_4717562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717562).length < 2 ^ (prefixWord ++ tailWord_4717562).sum := by decide
  have hdescent : baseEnd_4717562 < baseStart_4717562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717579 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 4, 4]
def baseStart_4717579 : Nat := 118140960795 + 4717579 * 2 ^ 59
def prefixEnd_4717579 : Nat := 4983230072969 + 3 ^ 40 * 4717579 * 2
def baseEnd_4717579 : Nat := 807461850852367728055585

theorem tailTrace_4717579 : CollatzResearch.WordTrace tailWord_4717579 prefixEnd_4717579 807461850852367728055585 := by
  unfold tailWord_4717579
  simp only [CollatzResearch.WordTrace]
  refine ⟨172064241776024456193387791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114709494517349637462258527 172064241776024456193387791)
  ·
    refine ⟨258096362664036684290081687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172064241776024456193387791 258096362664036684290081687)
    ·
      refine ⟨387144543996055026435122531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258096362664036684290081687 387144543996055026435122531)
      ·
        refine ⟨580716815994082539652683797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387144543996055026435122531 580716815994082539652683797)
        ·
          refine ⟨27221100749722619046219553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 580716815994082539652683797 27221100749722619046219553)
          ·
            refine ⟨20415825562291964284664665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27221100749722619046219553 20415825562291964284664665)
            ·
              refine ⟨15311869171718973213498499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20415825562291964284664665 15311869171718973213498499)
              ·
                refine ⟨22967803757578459820247749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15311869171718973213498499 22967803757578459820247749)
                ·
                  refine ⟨4306463204545961216296453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22967803757578459820247749 4306463204545961216296453)
                  ·
                    refine ⟨807461850852367728055585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4306463204545961216296453 807461850852367728055585)
                    ·
                      rfl

theorem cell23_4717579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 4].length) (baseStart_4717579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717579 prefixEnd_4717579 := by exact prefixLift 4717579
  have htrace : WordTrace (prefixWord ++ tailWord_4717579) baseStart_4717579 baseEnd_4717579 := by
    simpa [prefixWord, tailWord_4717579, baseEnd_4717579] using wordTrace_append hprefix tailTrace_4717579
  have hstable : (prefixWord ++ tailWord_4717579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717579).length < 2 ^ (prefixWord ++ tailWord_4717579).sum := by decide
  have hdescent : baseEnd_4717579 < baseStart_4717579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717580 : List Nat := [2, 2, 1, 2, 3, 3, 3, 2, 1, 1, 3]
def baseStart_4717580 : Nat := 118140960795 + 4717580 * 2 ^ 59
def prefixEnd_4717580 : Nat := 4983230072969 + 3 ^ 40 * 4717580 * 2
def baseEnd_4717580 : Nat := 2422386066037757680254251

theorem tailTrace_4717580 : CollatzResearch.WordTrace tailWord_4717580 prefixEnd_4717580 2422386066037757680254251 := by
  unfold tailWord_4717580
  simp only [CollatzResearch.WordTrace]
  refine ⟨86032139124510416682087097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114709518832680555576116129 86032139124510416682087097)
  ·
    refine ⟨64524104343382812511565323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86032139124510416682087097 64524104343382812511565323)
    ·
      refine ⟨96786156515074218767347985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64524104343382812511565323 96786156515074218767347985)
      ·
        refine ⟨72589617386305664075510989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96786156515074218767347985 72589617386305664075510989)
        ·
          refine ⟨27221106519864624028316621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72589617386305664075510989 27221106519864624028316621)
          ·
            refine ⟨10207914944949234010618733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27221106519864624028316621 10207914944949234010618733)
            ·
              refine ⟨3827968104355962753982025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10207914944949234010618733 3827968104355962753982025)
              ·
                refine ⟨2870976078266972065486519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3827968104355962753982025 2870976078266972065486519)
                ·
                  refine ⟨4306464117400458098229779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870976078266972065486519 4306464117400458098229779)
                  ·
                    refine ⟨6459696176100687147344669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4306464117400458098229779 6459696176100687147344669)
                    ·
                      refine ⟨2422386066037757680254251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6459696176100687147344669 2422386066037757680254251)
                      ·
                        rfl

theorem cell23_4717580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_4717580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717580 prefixEnd_4717580 := by exact prefixLift 4717580
  have htrace : WordTrace (prefixWord ++ tailWord_4717580) baseStart_4717580 baseEnd_4717580 := by
    simpa [prefixWord, tailWord_4717580, baseEnd_4717580] using wordTrace_append hprefix tailTrace_4717580
  have hstable : (prefixWord ++ tailWord_4717580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717580).length < 2 ^ (prefixWord ++ tailWord_4717580).sum := by decide
  have hdescent : baseEnd_4717580 < baseStart_4717580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717589 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_4717589 : Nat := 118140960795 + 4717589 * 2 ^ 59
def prefixEnd_4717589 : Nat := 4983230072969 + 3 ^ 40 * 4717589 * 2
def baseEnd_4717589 : Nat := 2422390687363648145041709

theorem tailTrace_4717589 : CollatzResearch.WordTrace tailWord_4717589 prefixEnd_4717589 2422390687363648145041709 := by
  unfold tailWord_4717589
  simp only [CollatzResearch.WordTrace]
  refine ⟨172064606505988227901251821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114709737670658818600834547 172064606505988227901251821)
  ·
    refine ⟨64524227439745585462969433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172064606505988227901251821 64524227439745585462969433)
    ·
      refine ⟨48393170579809189097227075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64524227439745585462969433 48393170579809189097227075)
      ·
        refine ⟨72589755869713783645840613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48393170579809189097227075 72589755869713783645840613)
        ·
          refine ⟨13610579225571334433595115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72589755869713783645840613 13610579225571334433595115)
          ·
            refine ⟨20415868838357001650392673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13610579225571334433595115 20415868838357001650392673)
            ·
              refine ⟨15311901628767751237794505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20415868838357001650392673 15311901628767751237794505)
              ·
                refine ⟨11483926221575813428345879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15311901628767751237794505 11483926221575813428345879)
                ·
                  refine ⟨17225889332363720142518819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11483926221575813428345879 17225889332363720142518819)
                  ·
                    refine ⟨25838833998545580213778229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17225889332363720142518819 25838833998545580213778229)
                    ·
                      refine ⟨2422390687363648145041709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25838833998545580213778229 2422390687363648145041709)
                      ·
                        rfl

theorem cell23_4717589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_4717589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717589 prefixEnd_4717589 := by exact prefixLift 4717589
  have htrace : WordTrace (prefixWord ++ tailWord_4717589) baseStart_4717589 baseEnd_4717589 := by
    simpa [prefixWord, tailWord_4717589, baseEnd_4717589] using wordTrace_append hprefix tailTrace_4717589
  have hstable : (prefixWord ++ tailWord_4717589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717589).length < 2 ^ (prefixWord ++ tailWord_4717589).sum := by decide
  have hdescent : baseEnd_4717589 < baseStart_4717589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717592 : List Nat := [2, 1, 2, 3, 2, 2, 1, 10]
def baseStart_4717592 : Nat := 118140960795 + 4717592 * 2 ^ 59
def prefixEnd_4717592 : Nat := 4983230072969 + 3 ^ 40 * 4717592 * 2
def baseEnd_4717592 : Nat := 89718230659467097529785

theorem tailTrace_4717592 : CollatzResearch.WordTrace tailWord_4717592 prefixEnd_4717592 89718230659467097529785 := by
  unfold tailWord_4717592
  simp only [CollatzResearch.WordTrace]
  refine ⟨86032357962488679706805515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114709810616651572942407353 86032357962488679706805515)
  ·
    refine ⟨129048536943733019560208273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86032357962488679706805515 129048536943733019560208273)
    ·
      refine ⟨96786402707799764670156205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129048536943733019560208273 96786402707799764670156205)
      ·
        refine ⟨36294901015424911751308577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96786402707799764670156205 36294901015424911751308577)
        ·
          refine ⟨27221175761568683813481433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36294901015424911751308577 27221175761568683813481433)
          ·
            refine ⟨20415881821176512860111075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27221175761568683813481433 20415881821176512860111075)
            ·
              refine ⟨30623822731764769290166613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20415881821176512860111075 30623822731764769290166613)
              ·
                refine ⟨89718230659467097529785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30623822731764769290166613 89718230659467097529785)
                ·
                  rfl

theorem cell23_4717592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 10].length) (baseStart_4717592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717592 prefixEnd_4717592 := by exact prefixLift 4717592
  have htrace : WordTrace (prefixWord ++ tailWord_4717592) baseStart_4717592 baseEnd_4717592 := by
    simpa [prefixWord, tailWord_4717592, baseEnd_4717592] using wordTrace_append hprefix tailTrace_4717592
  have hstable : (prefixWord ++ tailWord_4717592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717592).length < 2 ^ (prefixWord ++ tailWord_4717592).sum := by decide
  have hdescent : baseEnd_4717592 < baseStart_4717592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717600 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 1, 5]
def baseStart_4717600 : Nat := 118140960795 + 4717600 * 2 ^ 59
def prefixEnd_4717600 : Nat := 4983230072969 + 3 ^ 40 * 4717600 * 2
def baseEnd_4717600 : Nat := 807465445216949200668053

theorem tailTrace_4717600 : CollatzResearch.WordTrace tailWord_4717600 prefixEnd_4717600 807465445216949200668053 := by
  unfold tailWord_4717600
  simp only [CollatzResearch.WordTrace]
  refine ⟨86032503854474188389951127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114710005139298917853268169 86032503854474188389951127)
  ·
    refine ⟨129048755781711282584926691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86032503854474188389951127 129048755781711282584926691)
    ·
      refine ⟨193573133672566923877390037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129048755781711282584926691 193573133672566923877390037)
      ·
        refine ⟨4536870320450787278376329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 193573133672566923877390037 4536870320450787278376329)
        ·
          refine ⟨3402652740338090458782247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4536870320450787278376329 3402652740338090458782247)
          ·
            refine ⟨5103979110507135688173371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3402652740338090458782247 5103979110507135688173371)
            ·
              refine ⟨7655968665760703532260057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103979110507135688173371 7655968665760703532260057)
              ·
                refine ⟨5741976499320527649195043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7655968665760703532260057 5741976499320527649195043)
                ·
                  refine ⟨8612964748980791473792565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5741976499320527649195043 8612964748980791473792565)
                  ·
                    refine ⟨807465445216949200668053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8612964748980791473792565 807465445216949200668053)
                    ·
                      rfl

theorem cell23_4717600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 5].length) (baseStart_4717600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717600 prefixEnd_4717600 := by exact prefixLift 4717600
  have htrace : WordTrace (prefixWord ++ tailWord_4717600) baseStart_4717600 baseEnd_4717600 := by
    simpa [prefixWord, tailWord_4717600, baseEnd_4717600] using wordTrace_append hprefix tailTrace_4717600
  have hstable : (prefixWord ++ tailWord_4717600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717600).length < 2 ^ (prefixWord ++ tailWord_4717600).sum := by decide
  have hdescent : baseEnd_4717600 < baseStart_4717600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717620 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_4717620 : Nat := 118140960795 + 4717620 * 2 ^ 59
def prefixEnd_4717620 : Nat := 4983230072969 + 3 ^ 40 * 4717620 * 2
def baseEnd_4717620 : Nat := 2422406605263937523754067

theorem tailTrace_4717620 : CollatzResearch.WordTrace tailWord_4717620 prefixEnd_4717620 2422406605263937523754067 := by
  unfold tailWord_4717620
  simp only [CollatzResearch.WordTrace]
  refine ⟨86032868584437960097815157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114710491445917280130420209 86032868584437960097815157)
  ·
    refine ⟨8065581429791058759170171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86032868584437960097815157 8065581429791058759170171)
    ·
      refine ⟨12098372144686588138755257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8065581429791058759170171 12098372144686588138755257)
      ·
        refine ⟨9073779108514941104066443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12098372144686588138755257 9073779108514941104066443)
        ·
          refine ⟨13610668662772411656099665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073779108514941104066443 13610668662772411656099665)
          ·
            refine ⟨10208001497079308742074749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13610668662772411656099665 10208001497079308742074749)
            ·
              refine ⟨3828000561404740778278031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10208001497079308742074749 3828000561404740778278031)
              ·
                refine ⟨5742000842107111167417047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828000561404740778278031 5742000842107111167417047)
                ·
                  refine ⟨8613001263160666751125571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5742000842107111167417047 8613001263160666751125571)
                  ·
                    refine ⟨12919501894741000126688357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8613001263160666751125571 12919501894741000126688357)
                    ·
                      refine ⟨2422406605263937523754067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12919501894741000126688357 2422406605263937523754067)
                      ·
                        rfl

theorem cell23_4717620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_4717620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717620 prefixEnd_4717620 := by exact prefixLift 4717620
  have htrace : WordTrace (prefixWord ++ tailWord_4717620) baseStart_4717620 baseEnd_4717620 := by
    simpa [prefixWord, tailWord_4717620, baseEnd_4717620] using wordTrace_append hprefix tailTrace_4717620
  have hstable : (prefixWord ++ tailWord_4717620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717620).length < 2 ^ (prefixWord ++ tailWord_4717620).sum := by decide
  have hdescent : baseEnd_4717620 < baseStart_4717620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717646 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_4717646 : Nat := 118140960795 + 4717646 * 2 ^ 59
def prefixEnd_4717646 : Nat := 4983230072969 + 3 ^ 40 * 4717646 * 2
def baseEnd_4717646 : Nat := 2422419955760954422028947

theorem tailTrace_4717646 : CollatzResearch.WordTrace tailWord_4717646 prefixEnd_4717646 2422419955760954422028947 := by
  unfold tailWord_4717646
  simp only [CollatzResearch.WordTrace]
  refine ⟨21508335683347715829509599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114711123644521151090717861 21508335683347715829509599)
  ·
    refine ⟨32262503525021573744264399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21508335683347715829509599 32262503525021573744264399)
    ·
      refine ⟨48393755287532360616396599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32262503525021573744264399 48393755287532360616396599)
      ·
        refine ⟨72590632931298540924594899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48393755287532360616396599 72590632931298540924594899)
        ·
          refine ⟨108885949396947811386892349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72590632931298540924594899 108885949396947811386892349)
          ·
            refine ⟨40832231023855429270084631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108885949396947811386892349 40832231023855429270084631)
            ·
              refine ⟨61248346535783143905126947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40832231023855429270084631 61248346535783143905126947)
              ·
                refine ⟨91872519803674715857690421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61248346535783143905126947 91872519803674715857690421)
                ·
                  refine ⟨8613048731594504611658477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91872519803674715857690421 8613048731594504611658477)
                  ·
                    refine ⟨3229893274347939229371929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8613048731594504611658477 3229893274347939229371929)
                    ·
                      refine ⟨2422419955760954422028947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229893274347939229371929 2422419955760954422028947)
                      ·
                        rfl

theorem cell23_4717646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_4717646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717646 prefixEnd_4717646 := by exact prefixLift 4717646
  have htrace : WordTrace (prefixWord ++ tailWord_4717646) baseStart_4717646 baseEnd_4717646 := by
    simpa [prefixWord, tailWord_4717646, baseEnd_4717646] using wordTrace_append hprefix tailTrace_4717646
  have hstable : (prefixWord ++ tailWord_4717646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717646).length < 2 ^ (prefixWord ++ tailWord_4717646).sum := by decide
  have hdescent : baseEnd_4717646 < baseStart_4717646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717676 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 1, 4, 2]
def baseStart_4717676 : Nat := 118140960795 + 4717676 * 2 ^ 59
def prefixEnd_4717676 : Nat := 4983230072969 + 3 ^ 40 * 4717676 * 2
def baseEnd_4717676 : Nat := 2422435360180589304653809

theorem tailTrace_4717676 : CollatzResearch.WordTrace tailWord_4717676 prefixEnd_4717676 2422435360180589304653809 := by
  unfold tailWord_4717676
  simp only [CollatzResearch.WordTrace]
  refine ⟨86033889828336520879834441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114711853104448694506445921 86033889828336520879834441)
  ·
    refine ⟨64525417371252390659875831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86033889828336520879834441 64525417371252390659875831)
    ·
      refine ⟨96788126056878585989813747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64525417371252390659875831 96788126056878585989813747)
      ·
        refine ⟨145182189085317878984720621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96788126056878585989813747 145182189085317878984720621)
        ·
          refine ⟨54443320906994204619270233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145182189085317878984720621 54443320906994204619270233)
          ·
            refine ⟨40832490680245653464452675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54443320906994204619270233 40832490680245653464452675)
            ·
              refine ⟨61248736020368480196679013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40832490680245653464452675 61248736020368480196679013)
              ·
                refine ⟨11484138003819090036877315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61248736020368480196679013 11484138003819090036877315)
                ·
                  refine ⟨17226207005728635055315973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11484138003819090036877315 17226207005728635055315973)
                  ·
                    refine ⟨3229913813574119072871745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17226207005728635055315973 3229913813574119072871745)
                    ·
                      refine ⟨2422435360180589304653809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229913813574119072871745 2422435360180589304653809)
                      ·
                        rfl

theorem cell23_4717676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_4717676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717676 prefixEnd_4717676 := by exact prefixLift 4717676
  have htrace : WordTrace (prefixWord ++ tailWord_4717676) baseStart_4717676 baseEnd_4717676 := by
    simpa [prefixWord, tailWord_4717676, baseEnd_4717676] using wordTrace_append hprefix tailTrace_4717676
  have hstable : (prefixWord ++ tailWord_4717676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717676).length < 2 ^ (prefixWord ++ tailWord_4717676).sum := by decide
  have hdescent : baseEnd_4717676 < baseStart_4717676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717693 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_4717693 : Nat := 118140960795 + 4717693 * 2 ^ 59
def prefixEnd_4717693 : Nat := 4983230072969 + 3 ^ 40 * 4717693 * 2
def baseEnd_4717693 : Nat := 2422444089351715738141231

theorem tailTrace_4717693 : CollatzResearch.WordTrace tailWord_4717693 prefixEnd_4717693 2422444089351715738141231 := by
  unfold tailWord_4717693
  simp only [CollatzResearch.WordTrace]
  refine ⟨172068399697611453663037733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114712266465074302442025155 172068399697611453663037733)
  ·
    refine ⟨32262824943302147561819575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172068399697611453663037733 32262824943302147561819575)
    ·
      refine ⟨48394237414953221342729363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32262824943302147561819575 48394237414953221342729363)
      ·
        refine ⟨72591356122429832014094045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48394237414953221342729363 72591356122429832014094045)
        ·
          refine ⟨27221758545911187005285267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72591356122429832014094045 27221758545911187005285267)
          ·
            refine ⟨40832637818866780507927901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27221758545911187005285267 40832637818866780507927901)
            ·
              refine ⟨15312239182075042690472963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40832637818866780507927901 15312239182075042690472963)
              ·
                refine ⟨22968358773112564035709445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15312239182075042690472963 22968358773112564035709445)
                ·
                  refine ⟨4306567269958605756695521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22968358773112564035709445 4306567269958605756695521)
                  ·
                    refine ⟨3229925452468954317521641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4306567269958605756695521 3229925452468954317521641)
                    ·
                      refine ⟨2422444089351715738141231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229925452468954317521641 2422444089351715738141231)
                      ·
                        rfl

theorem cell23_4717693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_4717693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717693 prefixEnd_4717693 := by exact prefixLift 4717693
  have htrace : WordTrace (prefixWord ++ tailWord_4717693) baseStart_4717693 baseEnd_4717693 := by
    simpa [prefixWord, tailWord_4717693, baseEnd_4717693] using wordTrace_append hprefix tailTrace_4717693
  have hstable : (prefixWord ++ tailWord_4717693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717693).length < 2 ^ (prefixWord ++ tailWord_4717693).sum := by decide
  have hdescent : baseEnd_4717693 < baseStart_4717693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717699 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 7]
def baseStart_4717699 : Nat := 118140960795 + 4717699 * 2 ^ 59
def prefixEnd_4717699 : Nat := 4983230072969 + 3 ^ 40 * 4717699 * 2
def baseEnd_4717699 : Nat := 269160796692849190518467

theorem tailTrace_4717699 : CollatzResearch.WordTrace tailWord_4717699 prefixEnd_4717699 269160796692849190518467 := by
  unfold tailWord_4717699
  simp only [CollatzResearch.WordTrace]
  refine ⟨172068618535589716687756151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114712412357059811125170767 172068618535589716687756151)
  ·
    refine ⟨258102927803384575031634227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172068618535589716687756151 258102927803384575031634227)
    ·
      refine ⟨387154391705076862547451341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258102927803384575031634227 387154391705076862547451341)
      ·
        refine ⟨145182896889403823455294253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387154391705076862547451341 145182896889403823455294253)
        ·
          refine ⟨54443586333526433795735345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145182896889403823455294253 54443586333526433795735345)
          ·
            refine ⟨40832689750144825346801509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54443586333526433795735345 40832689750144825346801509)
            ·
              refine ⟨7656129328152154752525283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40832689750144825346801509 7656129328152154752525283)
              ·
                refine ⟨11484193992228232128787925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7656129328152154752525283 11484193992228232128787925)
                ·
                  refine ⟨269160796692849190518467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11484193992228232128787925 269160796692849190518467)
                  ·
                    rfl

theorem cell23_4717699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 7].length) (baseStart_4717699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717699 prefixEnd_4717699 := by exact prefixLift 4717699
  have htrace : WordTrace (prefixWord ++ tailWord_4717699) baseStart_4717699 baseEnd_4717699 := by
    simpa [prefixWord, tailWord_4717699, baseEnd_4717699] using wordTrace_append hprefix tailTrace_4717699
  have hstable : (prefixWord ++ tailWord_4717699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717699).length < 2 ^ (prefixWord ++ tailWord_4717699).sum := by decide
  have hdescent : baseEnd_4717699 < baseStart_4717699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717710 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_4717710 : Nat := 118140960795 + 4717710 * 2 ^ 59
def prefixEnd_4717710 : Nat := 4983230072969 + 3 ^ 40 * 4717710 * 2
def baseEnd_4717710 : Nat := 2422452818522842171628653

theorem tailTrace_4717710 : CollatzResearch.WordTrace tailWord_4717710 prefixEnd_4717710 2422452818522842171628653 := by
  unfold tailWord_4717710
  simp only [CollatzResearch.WordTrace]
  refine ⟨21508627467318733195800823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114712679825699910377604389 21508627467318733195800823)
  ·
    refine ⟨32262941200978099793701235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21508627467318733195800823 32262941200978099793701235)
    ·
      refine ⟨48394411801467149690551853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32262941200978099793701235 48394411801467149690551853)
      ·
        refine ⟨18147904425550181133956945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48394411801467149690551853 18147904425550181133956945)
        ·
          refine ⟨13610928319162635850467709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18147904425550181133956945 13610928319162635850467709)
          ·
            refine ⟨5104098119685988443925391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13610928319162635850467709 5104098119685988443925391)
            ·
              refine ⟨7656147179528982665888087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5104098119685988443925391 7656147179528982665888087)
              ·
                refine ⟨11484220769293473998832131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7656147179528982665888087 11484220769293473998832131)
                ·
                  refine ⟨17226331153940210998248197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11484220769293473998832131 17226331153940210998248197)
                  ·
                    refine ⟨3229937091363789562171537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17226331153940210998248197 3229937091363789562171537)
                    ·
                      refine ⟨2422452818522842171628653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3229937091363789562171537 2422452818522842171628653)
                      ·
                        rfl

theorem cell23_4717710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_4717710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717710 prefixEnd_4717710 := by exact prefixLift 4717710
  have htrace : WordTrace (prefixWord ++ tailWord_4717710) baseStart_4717710 baseEnd_4717710 := by
    simpa [prefixWord, tailWord_4717710, baseEnd_4717710] using wordTrace_append hprefix tailTrace_4717710
  have hstable : (prefixWord ++ tailWord_4717710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717710).length < 2 ^ (prefixWord ++ tailWord_4717710).sum := by decide
  have hdescent : baseEnd_4717710 < baseStart_4717710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717729 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 1, 7]
def baseStart_4717729 : Nat := 118140960795 + 4717729 * 2 ^ 59
def prefixEnd_4717729 : Nat := 4983230072969 + 3 ^ 40 * 4717729 * 2
def baseEnd_4717729 : Nat := 807487524885092532430355

theorem tailTrace_4717729 : CollatzResearch.WordTrace tailWord_4717729 prefixEnd_4717729 807487524885092532430355 := by
  unfold tailWord_4717729
  simp only [CollatzResearch.WordTrace]
  refine ⟨172069712725481031811348241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114713141816987354540898827 172069712725481031811348241)
  ·
    refine ⟨129052284544110773858511181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172069712725481031811348241 129052284544110773858511181)
    ·
      refine ⟨48394606704041540196941693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129052284544110773858511181 48394606704041540196941693)
      ·
        refine ⟨18147977514015577573853135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48394606704041540196941693 18147977514015577573853135)
        ·
          refine ⟨27221966271023366360779703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18147977514015577573853135 27221966271023366360779703)
          ·
            refine ⟨40832949406535049541169555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27221966271023366360779703 40832949406535049541169555)
            ·
              refine ⟨61249424109802574311754333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40832949406535049541169555 61249424109802574311754333)
              ·
                refine ⟨22968534041175965366907875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61249424109802574311754333 22968534041175965366907875)
                ·
                  refine ⟨34452801061763948050361813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22968534041175965366907875 34452801061763948050361813)
                  ·
                    refine ⟨807487524885092532430355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34452801061763948050361813 807487524885092532430355)
                    ·
                      rfl

theorem cell23_4717729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_4717729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717729 prefixEnd_4717729 := by exact prefixLift 4717729
  have htrace : WordTrace (prefixWord ++ tailWord_4717729) baseStart_4717729 baseEnd_4717729 := by
    simpa [prefixWord, tailWord_4717729, baseEnd_4717729] using wordTrace_append hprefix tailTrace_4717729
  have hstable : (prefixWord ++ tailWord_4717729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717729).length < 2 ^ (prefixWord ++ tailWord_4717729).sum := by decide
  have hdescent : baseEnd_4717729 < baseStart_4717729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717733 : List Nat := [1, 3, 1, 2, 1, 6, 1, 3, 5]
def baseStart_4717733 : Nat := 118140960795 + 4717733 * 2 ^ 59
def prefixEnd_4717733 : Nat := 4983230072969 + 3 ^ 40 * 4717733 * 2
def baseEnd_4717733 : Nat := 269162736508655064626783

theorem tailTrace_4717733 : CollatzResearch.WordTrace tailWord_4717733 prefixEnd_4717733 269162736508655064626783 := by
  unfold tailWord_4717733
  simp only [CollatzResearch.WordTrace]
  refine ⟨172069858617466540494493853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114713239078311026996329235 172069858617466540494493853)
  ·
    refine ⟨64526196981549952685435195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172069858617466540494493853 64526196981549952685435195)
    ·
      refine ⟨96789295472324929028152793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64526196981549952685435195 96789295472324929028152793)
      ·
        refine ⟨72591971604243696771114595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96789295472324929028152793 72591971604243696771114595)
        ·
          refine ⟨108887957406365545156671893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72591971604243696771114595 108887957406365545156671893)
          ·
            refine ⟨5104123003423384929218995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108887957406365545156671893 5104123003423384929218995)
            ·
              refine ⟨7656184505135077393828493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5104123003423384929218995 7656184505135077393828493)
              ·
                refine ⟨2871069189425654022685685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7656184505135077393828493 2871069189425654022685685)
                ·
                  refine ⟨269162736508655064626783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2871069189425654022685685 269162736508655064626783)
                  ·
                    rfl

theorem cell23_4717733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_4717733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717733 prefixEnd_4717733 := by exact prefixLift 4717733
  have htrace : WordTrace (prefixWord ++ tailWord_4717733) baseStart_4717733 baseEnd_4717733 := by
    simpa [prefixWord, tailWord_4717733, baseEnd_4717733] using wordTrace_append hprefix tailTrace_4717733
  have hstable : (prefixWord ++ tailWord_4717733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717733).length < 2 ^ (prefixWord ++ tailWord_4717733).sum := by decide
  have hdescent : baseEnd_4717733 < baseStart_4717733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717746 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_4717746 : Nat := 118140960795 + 4717746 * 2 ^ 59
def prefixEnd_4717746 : Nat := 4983230072969 + 3 ^ 40 * 4717746 * 2
def baseEnd_4717746 : Nat := 807490434608801343592829

theorem tailTrace_4717746 : CollatzResearch.WordTrace tailWord_4717746 prefixEnd_4717746 807490434608801343592829 := by
  unfold tailWord_4717746
  simp only [CollatzResearch.WordTrace]
  refine ⟨43017583191604860928679273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114713555177612962476478061 43017583191604860928679273)
  ·
    refine ⟨32263187393703645696509455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43017583191604860928679273 32263187393703645696509455)
    ·
      refine ⟨48394781090555468544764183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32263187393703645696509455 48394781090555468544764183)
      ·
        refine ⟨72592171635833202817146275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48394781090555468544764183 72592171635833202817146275)
        ·
          refine ⟨108888257453749804225719413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72592171635833202817146275 108888257453749804225719413)
          ·
            refine ⟨10208274136289044146161195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108888257453749804225719413 10208274136289044146161195)
            ·
              refine ⟨15312411204433566219241793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10208274136289044146161195 15312411204433566219241793)
              ·
                refine ⟨11484308403325174664431345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15312411204433566219241793 11484308403325174664431345)
                ·
                  refine ⟨8613231302493880998323509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11484308403325174664431345 8613231302493880998323509)
                  ·
                    refine ⟨807490434608801343592829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8613231302493880998323509 807490434608801343592829)
                    ·
                      rfl

theorem cell23_4717746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_4717746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717746 prefixEnd_4717746 := by exact prefixLift 4717746
  have htrace : WordTrace (prefixWord ++ tailWord_4717746) baseStart_4717746 baseEnd_4717746 := by
    simpa [prefixWord, tailWord_4717746, baseEnd_4717746] using wordTrace_append hprefix tailTrace_4717746
  have hstable : (prefixWord ++ tailWord_4717746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717746).length < 2 ^ (prefixWord ++ tailWord_4717746).sum := by decide
  have hdescent : baseEnd_4717746 < baseStart_4717746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717756 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4717756 : Nat := 118140960795 + 4717756 * 2 ^ 59
def prefixEnd_4717756 : Nat := 4983230072969 + 3 ^ 40 * 4717756 * 2
def baseEnd_4717756 : Nat := 2422476438632948991653441

theorem tailTrace_4717756 : CollatzResearch.WordTrace tailWord_4717756 prefixEnd_4717756 2422476438632948991653441 := by
  unfold tailWord_4717756
  simp only [CollatzResearch.WordTrace]
  refine ⟨86035348748191607711290561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114713798330922143615054081 86035348748191607711290561)
  ·
    refine ⟨64526511561143705783467921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86035348748191607711290561 64526511561143705783467921)
    ·
      refine ⟨48394883670857779337600941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64526511561143705783467921 48394883670857779337600941)
      ·
        refine ⟨18148081376571667251600353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48394883670857779337600941 18148081376571667251600353)
        ·
          refine ⟨13611061032428750438700265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18148081376571667251600353 13611061032428750438700265)
          ·
            refine ⟨10208295774321562829025199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13611061032428750438700265 10208295774321562829025199)
            ·
              refine ⟨15312443661482344243537799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10208295774321562829025199 15312443661482344243537799)
              ·
                refine ⟨22968665492223516365306699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15312443661482344243537799 22968665492223516365306699)
                ·
                  refine ⟨34452998238335274547960049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22968665492223516365306699 34452998238335274547960049)
                  ·
                    refine ⟨25839748678751455910970037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34452998238335274547960049 25839748678751455910970037)
                    ·
                      refine ⟨2422476438632948991653441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25839748678751455910970037 2422476438632948991653441)
                      ·
                        rfl

theorem cell23_4717756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4717756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717756 prefixEnd_4717756 := by exact prefixLift 4717756
  have htrace : WordTrace (prefixWord ++ tailWord_4717756) baseStart_4717756 baseEnd_4717756 := by
    simpa [prefixWord, tailWord_4717756, baseEnd_4717756] using wordTrace_append hprefix tailTrace_4717756
  have hstable : (prefixWord ++ tailWord_4717756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717756).length < 2 ^ (prefixWord ++ tailWord_4717756).sum := by decide
  have hdescent : baseEnd_4717756 < baseStart_4717756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717780 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_4717780 : Nat := 118140960795 + 4717780 * 2 ^ 59
def prefixEnd_4717780 : Nat := 4983230072969 + 3 ^ 40 * 4717780 * 2
def baseEnd_4717780 : Nat := 807496254056218965917777

theorem tailTrace_4717780 : CollatzResearch.WordTrace tailWord_4717780 prefixEnd_4717780 807496254056218965917777 := by
  unfold tailWord_4717780
  simp only [CollatzResearch.WordTrace]
  refine ⟨86035786424148133760727397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114714381898864178347636529 86035786424148133760727397)
  ·
    refine ⟨16131709954527775080136387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86035786424148133760727397 16131709954527775080136387)
    ·
      refine ⟨24197564931791662620204581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16131709954527775080136387 24197564931791662620204581)
      ·
        refine ⟨4537043424710936741288359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24197564931791662620204581 4537043424710936741288359)
        ·
          refine ⟨6805565137066405111932539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4537043424710936741288359 6805565137066405111932539)
          ·
            refine ⟨10208347705599607667898809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6805565137066405111932539 10208347705599607667898809)
            ·
              refine ⟨7656260779199705750924107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10208347705599607667898809 7656260779199705750924107)
              ·
                refine ⟨11484391168799558626386161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7656260779199705750924107 11484391168799558626386161)
                ·
                  refine ⟨8613293376599668969789621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11484391168799558626386161 8613293376599668969789621)
                  ·
                    refine ⟨807496254056218965917777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8613293376599668969789621 807496254056218965917777)
                    ·
                      rfl

theorem cell23_4717780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_4717780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717780 prefixEnd_4717780 := by exact prefixLift 4717780
  have htrace : WordTrace (prefixWord ++ tailWord_4717780) baseStart_4717780 baseEnd_4717780 := by
    simpa [prefixWord, tailWord_4717780, baseEnd_4717780] using wordTrace_append hprefix tailTrace_4717780
  have hstable : (prefixWord ++ tailWord_4717780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717780).length < 2 ^ (prefixWord ++ tailWord_4717780).sum := by decide
  have hdescent : baseEnd_4717780 < baseStart_4717780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717806 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_4717806 : Nat := 118140960795 + 4717806 * 2 ^ 59
def prefixEnd_4717806 : Nat := 4983230072969 + 3 ^ 40 * 4717806 * 2
def baseEnd_4717806 : Nat := 269166901407297088447579

theorem tailTrace_4717806 : CollatzResearch.WordTrace tailWord_4717806 prefixEnd_4717806 269166901407297088447579 := by
  unfold tailWord_4717806
  simp only [CollatzResearch.WordTrace]
  refine ⟨21509065143275259245237659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114715014097468049307934181 21509065143275259245237659)
  ·
    refine ⟨32263597714912888867856489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21509065143275259245237659 32263597714912888867856489)
    ·
      refine ⟨24197698286184666650892367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32263597714912888867856489 24197698286184666650892367)
      ·
        refine ⟨36296547429276999976338551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24197698286184666650892367 36296547429276999976338551)
        ·
          refine ⟨54444821143915499964507827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36296547429276999976338551 54444821143915499964507827)
          ·
            refine ⟨81667231715873249946761741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54444821143915499964507827 81667231715873249946761741)
            ·
              refine ⟨30625211893452468730035653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81667231715873249946761741 30625211893452468730035653)
              ·
                refine ⟨5742227230022337886881685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30625211893452468730035653 5742227230022337886881685)
                ·
                  refine ⟨269166901407297088447579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5742227230022337886881685 269166901407297088447579)
                  ·
                    rfl

theorem cell23_4717806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_4717806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717806 prefixEnd_4717806 := by exact prefixLift 4717806
  have htrace : WordTrace (prefixWord ++ tailWord_4717806) baseStart_4717806 baseEnd_4717806 := by
    simpa [prefixWord, tailWord_4717806, baseEnd_4717806] using wordTrace_append hprefix tailTrace_4717806
  have hstable : (prefixWord ++ tailWord_4717806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717806).length < 2 ^ (prefixWord ++ tailWord_4717806).sum := by decide
  have hdescent : baseEnd_4717806 < baseStart_4717806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717809 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_4717809 : Nat := 118140960795 + 4717809 * 2 ^ 59
def prefixEnd_4717809 : Nat := 4983230072969 + 3 ^ 40 * 4717809 * 2
def baseEnd_4717809 : Nat := 2422503653107637284290697

theorem tailTrace_4717809 : CollatzResearch.WordTrace tailWord_4717809 prefixEnd_4717809 2422503653107637284290697 := by
  unfold tailWord_4717809
  simp only [CollatzResearch.WordTrace]
  refine ⟨172072630565191205474260481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114715087043460803649506987 172072630565191205474260481)
  ·
    refine ⟨129054472923893404105695361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172072630565191205474260481 129054472923893404105695361)
    ·
      refine ⟨96790854692920053079271521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129054472923893404105695361 96790854692920053079271521)
      ·
        refine ⟨72593141019690039809453641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96790854692920053079271521 72593141019690039809453641)
        ·
          refine ⟨54444855764767529857090231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72593141019690039809453641 54444855764767529857090231)
          ·
            refine ⟨81667283647151294785635347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54444855764767529857090231 81667283647151294785635347)
            ·
              refine ⟨122500925470726942178453021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81667283647151294785635347 122500925470726942178453021)
              ·
                refine ⟨45937847051522603316919883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122500925470726942178453021 45937847051522603316919883)
                ·
                  refine ⟨68906770577283904975379825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45937847051522603316919883 68906770577283904975379825)
                  ·
                    refine ⟨51680077932962928731534869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68906770577283904975379825 51680077932962928731534869)
                    ·
                      refine ⟨2422503653107637284290697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51680077932962928731534869 2422503653107637284290697)
                      ·
                        rfl

theorem cell23_4717809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_4717809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717809 prefixEnd_4717809 := by exact prefixLift 4717809
  have htrace : WordTrace (prefixWord ++ tailWord_4717809) baseStart_4717809 baseEnd_4717809 := by
    simpa [prefixWord, tailWord_4717809, baseEnd_4717809] using wordTrace_append hprefix tailTrace_4717809
  have hstable : (prefixWord ++ tailWord_4717809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717809).length < 2 ^ (prefixWord ++ tailWord_4717809).sum := by decide
  have hdescent : baseEnd_4717809 < baseStart_4717809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717829 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_4717829 : Nat := 118140960795 + 4717829 * 2 ^ 59
def prefixEnd_4717829 : Nat := 4983230072969 + 3 ^ 40 * 4717829 * 2
def baseEnd_4717829 : Nat := 2422513922720727206040605

theorem tailTrace_4717829 : CollatzResearch.WordTrace tailWord_4717829 prefixEnd_4717829 2422513922720727206040605 := by
  unfold tailWord_4717829
  simp only [CollatzResearch.WordTrace]
  refine ⟨172073360025118748889988541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114715573350079165926659027 172073360025118748889988541)
  ·
    refine ⟨64527510009419530833745703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172073360025118748889988541 64527510009419530833745703)
    ·
      refine ⟨96791265014129296250618555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64527510009419530833745703 96791265014129296250618555)
      ·
        refine ⟨145186897521193944375927833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96791265014129296250618555 145186897521193944375927833)
        ·
          refine ⟨108890173140895458281945875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145186897521193944375927833 108890173140895458281945875)
          ·
            refine ⟨163335259711343187422918813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108890173140895458281945875 163335259711343187422918813)
            ·
              refine ⟨61250722391753695283594555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163335259711343187422918813 61250722391753695283594555)
              ·
                refine ⟨91876083587630542925391833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61250722391753695283594555 91876083587630542925391833)
                ·
                  refine ⟨68907062690722907194043875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91876083587630542925391833 68907062690722907194043875)
                  ·
                    refine ⟨103360594036084360791065813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68907062690722907194043875 103360594036084360791065813)
                    ·
                      refine ⟨2422513922720727206040605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103360594036084360791065813 2422513922720727206040605)
                      ·
                        rfl

theorem cell23_4717829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_4717829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717829 prefixEnd_4717829 := by exact prefixLift 4717829
  have htrace : WordTrace (prefixWord ++ tailWord_4717829) baseStart_4717829 baseEnd_4717829 := by
    simpa [prefixWord, tailWord_4717829, baseEnd_4717829] using wordTrace_append hprefix tailTrace_4717829
  have hstable : (prefixWord ++ tailWord_4717829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717829).length < 2 ^ (prefixWord ++ tailWord_4717829).sum := by decide
  have hdescent : baseEnd_4717829 < baseStart_4717829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717833 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 3]
def baseStart_4717833 : Nat := 118140960795 + 4717833 * 2 ^ 59
def prefixEnd_4717833 : Nat := 4983230072969 + 3 ^ 40 * 4717833 * 2
def baseEnd_4717833 : Nat := 2422515976643345190390587

theorem tailTrace_4717833 : CollatzResearch.WordTrace tailWord_4717833 prefixEnd_4717833 2422515976643345190390587 := by
  unfold tailWord_4717833
  simp only [CollatzResearch.WordTrace]
  refine ⟨172073505917104257573134153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114715670611402838382089435 172073505917104257573134153)
  ·
    refine ⟨129055129437828193179850615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172073505917104257573134153 129055129437828193179850615)
    ·
      refine ⟨193582694156742289769775923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129055129437828193179850615 193582694156742289769775923)
      ·
        refine ⟨290374041235113434654663885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193582694156742289769775923 290374041235113434654663885)
        ·
          refine ⟨108890265463167537995498957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290374041235113434654663885 108890265463167537995498957)
          ·
            refine ⟨40833849548687826748312109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108890265463167537995498957 40833849548687826748312109)
            ·
              refine ⟨15312693580757935030617041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40833849548687826748312109 15312693580757935030617041)
              ·
                refine ⟨11484520185568451272962781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15312693580757935030617041 11484520185568451272962781)
                ·
                  refine ⟨4306695069588169227361043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11484520185568451272962781 4306695069588169227361043)
                  ·
                    refine ⟨6460042604382253841041565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4306695069588169227361043 6460042604382253841041565)
                    ·
                      refine ⟨2422515976643345190390587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6460042604382253841041565 2422515976643345190390587)
                      ·
                        rfl

theorem cell23_4717833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 3].length) (baseStart_4717833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717833 prefixEnd_4717833 := by exact prefixLift 4717833
  have htrace : WordTrace (prefixWord ++ tailWord_4717833) baseStart_4717833 baseEnd_4717833 := by
    simpa [prefixWord, tailWord_4717833, baseEnd_4717833] using wordTrace_append hprefix tailTrace_4717833
  have hstable : (prefixWord ++ tailWord_4717833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717833).length < 2 ^ (prefixWord ++ tailWord_4717833).sum := by decide
  have hdescent : baseEnd_4717833 < baseStart_4717833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717836 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_4717836 : Nat := 118140960795 + 4717836 * 2 ^ 59
def prefixEnd_4717836 : Nat := 4983230072969 + 3 ^ 40 * 4717836 * 2
def baseEnd_4717836 : Nat := 807505839028436226217691

theorem tailTrace_4717836 : CollatzResearch.WordTrace tailWord_4717836 prefixEnd_4717836 807505839028436226217691 := by
  unfold tailWord_4717836
  simp only [CollatzResearch.WordTrace]
  refine ⟨86036807668046694542746681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114715743557395592723662241 86036807668046694542746681)
  ·
    refine ⟨64527605751035020907060011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86036807668046694542746681 64527605751035020907060011)
    ·
      refine ⟨96791408626552531360590017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64527605751035020907060011 96791408626552531360590017)
      ·
        refine ⟨72593556469914398520442513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96791408626552531360590017 72593556469914398520442513)
        ·
          refine ⟨54445167352435798890331885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72593556469914398520442513 54445167352435798890331885)
          ·
            refine ⟨20416937757163424583874457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54445167352435798890331885 20416937757163424583874457)
            ·
              refine ⟨15312703317872568437905843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20416937757163424583874457 15312703317872568437905843)
              ·
                refine ⟨22969054976808852656858765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15312703317872568437905843 22969054976808852656858765)
                ·
                  refine ⟨8613395616303319746322037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22969054976808852656858765 8613395616303319746322037)
                  ·
                    refine ⟨807505839028436226217691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8613395616303319746322037 807505839028436226217691)
                    ·
                      rfl

theorem cell23_4717836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_4717836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717836 prefixEnd_4717836 := by exact prefixLift 4717836
  have htrace : WordTrace (prefixWord ++ tailWord_4717836) baseStart_4717836 baseEnd_4717836 := by
    simpa [prefixWord, tailWord_4717836, baseEnd_4717836] using wordTrace_append hprefix tailTrace_4717836
  have hstable : (prefixWord ++ tailWord_4717836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717836).length < 2 ^ (prefixWord ++ tailWord_4717836).sum := by decide
  have hdescent : baseEnd_4717836 < baseStart_4717836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717946 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_4717946 : Nat := 118140960795 + 4717946 * 2 ^ 59
def prefixEnd_4717946 : Nat := 4983230072969 + 3 ^ 40 * 4717946 * 2
def baseEnd_4717946 : Nat := 2422573999957303248277567

theorem tailTrace_4717946 : CollatzResearch.WordTrace tailWord_4717946 prefixEnd_4717946 2422573999957303248277567 := by
  unfold tailWord_4717946
  simp only [CollatzResearch.WordTrace]
  refine ⟨43019406841423719467999423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114718418243796585247998461 43019406841423719467999423)
  ·
    refine ⟨64529110262135579201999135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43019406841423719467999423 64529110262135579201999135)
    ·
      refine ⟨96793665393203368802998703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64529110262135579201999135 96793665393203368802998703)
      ·
        refine ⟨145190498089805053204498055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96793665393203368802998703 145190498089805053204498055)
        ·
          refine ⟨217785747134707579806747083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145190498089805053204498055 217785747134707579806747083)
          ·
            refine ⟨326678620702061369710120625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217785747134707579806747083 326678620702061369710120625)
            ·
              refine ⟨245008965526546027282590469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326678620702061369710120625 245008965526546027282590469)
              ·
                refine ⟨45939181036227380115485713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245008965526546027282590469 45939181036227380115485713)
                ·
                  refine ⟨34454385777170535086614285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45939181036227380115485713 34454385777170535086614285)
                  ·
                    refine ⟨12920394666438950657480357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34454385777170535086614285 12920394666438950657480357)
                    ·
                      refine ⟨2422573999957303248277567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12920394666438950657480357 2422573999957303248277567)
                      ·
                        rfl

theorem cell23_4717946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_4717946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717946 prefixEnd_4717946 := by exact prefixLift 4717946
  have htrace : WordTrace (prefixWord ++ tailWord_4717946) baseStart_4717946 baseEnd_4717946 := by
    simpa [prefixWord, tailWord_4717946, baseEnd_4717946] using wordTrace_append hprefix tailTrace_4717946
  have hstable : (prefixWord ++ tailWord_4717946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717946).length < 2 ^ (prefixWord ++ tailWord_4717946).sum := by decide
  have hdescent : baseEnd_4717946 < baseStart_4717946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717983 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 3]
def baseStart_4717983 : Nat := 118140960795 + 4717983 * 2 ^ 59
def prefixEnd_4717983 : Nat := 4983230072969 + 3 ^ 40 * 4717983 * 2
def baseEnd_4717983 : Nat := 2422592998741519603514897

theorem tailTrace_4717983 : CollatzResearch.WordTrace tailWord_4717983 prefixEnd_4717983 2422592998741519603514897 := by
  unfold tailWord_4717983
  simp only [CollatzResearch.WordTrace]
  refine ⟨172078976866560833191094603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114719317911040555460729735 172078976866560833191094603)
  ·
    refine ⟨258118465299841249786641905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172078976866560833191094603 258118465299841249786641905)
    ·
      refine ⟨193588848974880937339981429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258118465299841249786641905 193588848974880937339981429)
      ·
        refine ⟨18148954591395087875623259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193588848974880937339981429 18148954591395087875623259)
        ·
          refine ⟨27223431887092631813434889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18148954591395087875623259 27223431887092631813434889)
          ·
            refine ⟨20417573915319473860076167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27223431887092631813434889 20417573915319473860076167)
            ·
              refine ⟨30626360872979210790114251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20417573915319473860076167 30626360872979210790114251)
              ·
                refine ⟨45939541309468816185171377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30626360872979210790114251 45939541309468816185171377)
                ·
                  refine ⟨34454655982101612138878533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45939541309468816185171377 34454655982101612138878533)
                  ·
                    refine ⟨6460247996644052276039725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34454655982101612138878533 6460247996644052276039725)
                    ·
                      refine ⟨2422592998741519603514897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6460247996644052276039725 2422592998741519603514897)
                      ·
                        rfl

theorem cell23_4717983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_4717983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717983 prefixEnd_4717983 := by exact prefixLift 4717983
  have htrace : WordTrace (prefixWord ++ tailWord_4717983) baseStart_4717983 baseEnd_4717983 := by
    simpa [prefixWord, tailWord_4717983, baseEnd_4717983] using wordTrace_append hprefix tailTrace_4717983
  have hstable : (prefixWord ++ tailWord_4717983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717983).length < 2 ^ (prefixWord ++ tailWord_4717983).sum := by decide
  have hdescent : baseEnd_4717983 < baseStart_4717983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4717997 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_4717997 : Nat := 118140960795 + 4717997 * 2 ^ 59
def prefixEnd_4717997 : Nat := 4983230072969 + 3 ^ 40 * 4717997 * 2
def baseEnd_4717997 : Nat := 2422600187470682548739833

theorem tailTrace_4717997 : CollatzResearch.WordTrace tailWord_4717997 prefixEnd_4717997 2422600187470682548739833 := by
  unfold tailWord_4717997
  simp only [CollatzResearch.WordTrace]
  refine ⟨172079487488510113582104245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114719658325673409054736163 172079487488510113582104245)
  ·
    refine ⟨16132451952047823148322273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172079487488510113582104245 16132451952047823148322273)
    ·
      refine ⟨12099338964035867361241705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16132451952047823148322273 12099338964035867361241705)
      ·
        refine ⟨9074504223026900520931279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12099338964035867361241705 9074504223026900520931279)
        ·
          refine ⟨13611756334540350781396919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9074504223026900520931279 13611756334540350781396919)
          ·
            refine ⟨20417634501810526172095379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13611756334540350781396919 20417634501810526172095379)
            ·
              refine ⟨30626451752715789258143069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20417634501810526172095379 30626451752715789258143069)
              ·
                refine ⟨11484919407268420971803651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30626451752715789258143069 11484919407268420971803651)
                ·
                  refine ⟨17227379110902631457705477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11484919407268420971803651 17227379110902631457705477)
                  ·
                    refine ⟨3230133583294243398319777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17227379110902631457705477 3230133583294243398319777)
                    ·
                      refine ⟨2422600187470682548739833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230133583294243398319777 2422600187470682548739833)
                      ·
                        rfl

theorem cell23_4717997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_4717997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4717997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4717997 prefixEnd_4717997 := by exact prefixLift 4717997
  have htrace : WordTrace (prefixWord ++ tailWord_4717997) baseStart_4717997 baseEnd_4717997 := by
    simpa [prefixWord, tailWord_4717997, baseEnd_4717997] using wordTrace_append hprefix tailTrace_4717997
  have hstable : (prefixWord ++ tailWord_4717997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4717997).length < 2 ^ (prefixWord ++ tailWord_4717997).sum := by decide
  have hdescent : baseEnd_4717997 < baseStart_4717997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4717997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718013 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_4718013 : Nat := 118140960795 + 4718013 * 2 ^ 59
def prefixEnd_4718013 : Nat := 4983230072969 + 3 ^ 40 * 4718013 * 2
def baseEnd_4718013 : Nat := 2422608403161154486139759

theorem tailTrace_4718013 : CollatzResearch.WordTrace tailWord_4718013 prefixEnd_4718013 2422608403161154486139759 := by
  unfold tailWord_4718013
  simp only [CollatzResearch.WordTrace]
  refine ⟨172080071056452148314686693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114720047370968098876457795 172080071056452148314686693)
  ·
    refine ⟨32265013323084777809003755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172080071056452148314686693 32265013323084777809003755)
    ·
      refine ⟨48397519984627166713505633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32265013323084777809003755 48397519984627166713505633)
      ·
        refine ⟨36298139988470375035129225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48397519984627166713505633 36298139988470375035129225)
        ·
          refine ⟨27223604991352781276346919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36298139988470375035129225 27223604991352781276346919)
          ·
            refine ⟨40835407487029171914520379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27223604991352781276346919 40835407487029171914520379)
            ·
              refine ⟨61253111230543757871780569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40835407487029171914520379 61253111230543757871780569)
              ·
                refine ⟨45939833422907818403835427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61253111230543757871780569 45939833422907818403835427)
                ·
                  refine ⟨68909750134361727605753141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45939833422907818403835427 68909750134361727605753141)
                  ·
                    refine ⟨6460289075096411963039357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68909750134361727605753141 6460289075096411963039357)
                    ·
                      refine ⟨2422608403161154486139759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6460289075096411963039357 2422608403161154486139759)
                      ·
                        rfl

theorem cell23_4718013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_4718013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718013 prefixEnd_4718013 := by exact prefixLift 4718013
  have htrace : WordTrace (prefixWord ++ tailWord_4718013) baseStart_4718013 baseEnd_4718013 := by
    simpa [prefixWord, tailWord_4718013, baseEnd_4718013] using wordTrace_append hprefix tailTrace_4718013
  have hstable : (prefixWord ++ tailWord_4718013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718013).length < 2 ^ (prefixWord ++ tailWord_4718013).sum := by decide
  have hdescent : baseEnd_4718013 < baseStart_4718013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718070 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4718070 : Nat := 118140960795 + 4718070 * 2 ^ 59
def prefixEnd_4718070 : Nat := 4983230072969 + 3 ^ 40 * 4718070 * 2
def baseEnd_4718070 : Nat := 2422637671558460763126997

theorem tailTrace_4718070 : CollatzResearch.WordTrace tailWord_4718070 prefixEnd_4718070 2422637671558460763126997 := by
  unfold tailWord_4718070
  simp only [CollatzResearch.WordTrace]
  refine ⟨10755134376077852940594479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114721433344830431366341109 10755134376077852940594479)
  ·
    refine ⟨16132701564116779410891719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10755134376077852940594479 16132701564116779410891719)
    ·
      refine ⟨24199052346175169116337579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16132701564116779410891719 24199052346175169116337579)
      ·
        refine ⟨36298578519262753674506369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24199052346175169116337579 36298578519262753674506369)
        ·
          refine ⟨27223933889447065255879777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36298578519262753674506369 27223933889447065255879777)
          ·
            refine ⟨20417950417085298941909833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27223933889447065255879777 20417950417085298941909833)
            ·
              refine ⟨15313462812813974206432375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20417950417085298941909833 15313462812813974206432375)
              ·
                refine ⟨22970194219220961309648563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15313462812813974206432375 22970194219220961309648563)
                ·
                  refine ⟨34455291328831441964472845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22970194219220961309648563 34455291328831441964472845)
                  ·
                    refine ⟨12920734248311790736677317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34455291328831441964472845 12920734248311790736677317)
                    ·
                      refine ⟨2422637671558460763126997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12920734248311790736677317 2422637671558460763126997)
                      ·
                        rfl

theorem cell23_4718070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4718070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718070 prefixEnd_4718070 := by exact prefixLift 4718070
  have htrace : WordTrace (prefixWord ++ tailWord_4718070) baseStart_4718070 baseEnd_4718070 := by
    simpa [prefixWord, tailWord_4718070, baseEnd_4718070] using wordTrace_append hprefix tailTrace_4718070
  have hstable : (prefixWord ++ tailWord_4718070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718070).length < 2 ^ (prefixWord ++ tailWord_4718070).sum := by decide
  have hdescent : baseEnd_4718070 < baseStart_4718070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718090 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_4718090 : Nat := 118140960795 + 4718090 * 2 ^ 59
def prefixEnd_4718090 : Nat := 4983230072969 + 3 ^ 40 * 4718090 * 2
def baseEnd_4718090 : Nat := 2422647941171550684876905

theorem tailTrace_4718090 : CollatzResearch.WordTrace tailWord_4718090 prefixEnd_4718090 2422647941171550684876905 := by
  unfold tailWord_4718090
  simp only [CollatzResearch.WordTrace]
  refine ⟨43020719869293297616309931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114721919651448793643493149 43020719869293297616309931)
  ·
    refine ⟨64531079803939946424464897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43020719869293297616309931 64531079803939946424464897)
    ·
      refine ⟨48398309852954959818348673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64531079803939946424464897 48398309852954959818348673)
      ·
        refine ⟨36298732389716219863761505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48398309852954959818348673 36298732389716219863761505)
        ·
          refine ⟨27224049292287164897821129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36298732389716219863761505 27224049292287164897821129)
          ·
            refine ⟨20418036969215373673365847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27224049292287164897821129 20418036969215373673365847)
            ·
              refine ⟨30627055453823060510048771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20418036969215373673365847 30627055453823060510048771)
              ·
                refine ⟨45940583180734590765073157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30627055453823060510048771 45940583180734590765073157)
                ·
                  refine ⟨8613859346387735768451217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45940583180734590765073157 8613859346387735768451217)
                  ·
                    refine ⟨6460394509790801826338413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8613859346387735768451217 6460394509790801826338413)
                    ·
                      refine ⟨2422647941171550684876905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6460394509790801826338413 2422647941171550684876905)
                      ·
                        rfl

theorem cell23_4718090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_4718090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718090 prefixEnd_4718090 := by exact prefixLift 4718090
  have htrace : WordTrace (prefixWord ++ tailWord_4718090) baseStart_4718090 baseEnd_4718090 := by
    simpa [prefixWord, tailWord_4718090, baseEnd_4718090] using wordTrace_append hprefix tailTrace_4718090
  have hstable : (prefixWord ++ tailWord_4718090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718090).length < 2 ^ (prefixWord ++ tailWord_4718090).sum := by decide
  have hdescent : baseEnd_4718090 < baseStart_4718090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718154 : List Nat := [3, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_4718154 : Nat := 118140960795 + 4718154 * 2 ^ 59
def prefixEnd_4718154 : Nat := 4983230072969 + 3 ^ 40 * 4718154 * 2
def baseEnd_4718154 : Nat := 2422680803933438434476611

theorem tailTrace_4718154 : CollatzResearch.WordTrace tailWord_4718154 prefixEnd_4718154 2422680803933438434476611 := by
  unfold tailWord_4718154
  simp only [CollatzResearch.WordTrace]
  refine ⟨43021303437235332348892379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114723475832627552930379677 43021303437235332348892379)
  ·
    refine ⟨64531955155852998523338569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43021303437235332348892379 64531955155852998523338569)
    ·
      refine ⟨48398966366889748892503927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64531955155852998523338569 48398966366889748892503927)
      ·
        refine ⟨72598449550334623338755891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48398966366889748892503927 72598449550334623338755891)
        ·
          refine ⟨108897674325501935008133837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72598449550334623338755891 108897674325501935008133837)
          ·
            refine ⟨40836627872063225628050189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108897674325501935008133837 40836627872063225628050189)
            ·
              refine ⟨15313735452023709610518821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40836627872063225628050189 15313735452023709610518821)
              ·
                refine ⟨2871325397254445551972279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15313735452023709610518821 2871325397254445551972279)
                ·
                  refine ⟨4306988095881668327958419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871325397254445551972279 4306988095881668327958419)
                  ·
                    refine ⟨6460482143822502491937629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4306988095881668327958419 6460482143822502491937629)
                    ·
                      refine ⟨2422680803933438434476611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6460482143822502491937629 2422680803933438434476611)
                      ·
                        rfl

theorem cell23_4718154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_4718154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718154 prefixEnd_4718154 := by exact prefixLift 4718154
  have htrace : WordTrace (prefixWord ++ tailWord_4718154) baseStart_4718154 baseEnd_4718154 := by
    simpa [prefixWord, tailWord_4718154, baseEnd_4718154] using wordTrace_append hprefix tailTrace_4718154
  have hstable : (prefixWord ++ tailWord_4718154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718154).length < 2 ^ (prefixWord ++ tailWord_4718154).sum := by decide
  have hdescent : baseEnd_4718154 < baseStart_4718154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718183 : List Nat := [1, 1, 5, 1, 1, 1, 2, 11]
def baseStart_4718183 : Nat := 118140960795 + 4718183 * 2 ^ 59
def prefixEnd_4718183 : Nat := 4983230072969 + 3 ^ 40 * 4718183 * 2
def baseEnd_4718183 : Nat := 89729470180459956333851

theorem tailTrace_4718183 : CollatzResearch.WordTrace tailWord_4718183 prefixEnd_4718183 89729470180459956333851 := by
  unfold tailWord_4718183
  simp only [CollatzResearch.WordTrace]
  refine ⟨172086271465836267348375203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114724180977224178232250135 172086271465836267348375203)
  ·
    refine ⟨258129407198754401022562805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172086271465836267348375203 258129407198754401022562805)
    ·
      refine ⟨24199631924883225095865263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 258129407198754401022562805 24199631924883225095865263)
      ·
        refine ⟨36299447887324837643797895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24199631924883225095865263 36299447887324837643797895)
        ·
          refine ⟨54449171830987256465696843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36299447887324837643797895 54449171830987256465696843)
          ·
            refine ⟨81673757746480884698545265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54449171830987256465696843 81673757746480884698545265)
            ·
              refine ⟨61255318309860663523908949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81673757746480884698545265 61255318309860663523908949)
              ·
                refine ⟨89729470180459956333851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 61255318309860663523908949 89729470180459956333851)
                ·
                  rfl

theorem cell23_4718183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 11].length) (baseStart_4718183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718183 prefixEnd_4718183 := by exact prefixLift 4718183
  have htrace : WordTrace (prefixWord ++ tailWord_4718183) baseStart_4718183 baseEnd_4718183 := by
    simpa [prefixWord, tailWord_4718183, baseEnd_4718183] using wordTrace_append hprefix tailTrace_4718183
  have hstable : (prefixWord ++ tailWord_4718183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718183).length < 2 ^ (prefixWord ++ tailWord_4718183).sum := by decide
  have hdescent : baseEnd_4718183 < baseStart_4718183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718194 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_4718194 : Nat := 118140960795 + 4718194 * 2 ^ 59
def prefixEnd_4718194 : Nat := 4983230072969 + 3 ^ 40 * 4718194 * 2
def baseEnd_4718194 : Nat := 2422701343159618277976427

theorem tailTrace_4718194 : CollatzResearch.WordTrace tailWord_4718194 prefixEnd_4718194 2422701343159618277976427 := by
  unfold tailWord_4718194
  simp only [CollatzResearch.WordTrace]
  refine ⟨43021668167199104056756409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114724448445864277484683757 43021668167199104056756409)
  ·
    refine ⟨32266251125399328042567307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43021668167199104056756409 32266251125399328042567307)
    ·
      refine ⟨48399376688098992063850961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32266251125399328042567307 48399376688098992063850961)
      ·
        refine ⟨36299532516074244047888221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48399376688098992063850961 36299532516074244047888221)
        ·
          refine ⟨13612324693527841517958083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36299532516074244047888221 13612324693527841517958083)
          ·
            refine ⟨20418487040291762276937125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13612324693527841517958083 20418487040291762276937125)
            ·
              refine ⟨3828466320054705426925711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20418487040291762276937125 3828466320054705426925711)
              ·
                refine ⟨5742699480082058140388567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828466320054705426925711 5742699480082058140388567)
                ·
                  refine ⟨8614049220123087210582851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5742699480082058140388567 8614049220123087210582851)
                  ·
                    refine ⟨12921073830184630815874277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8614049220123087210582851 12921073830184630815874277)
                    ·
                      refine ⟨2422701343159618277976427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12921073830184630815874277 2422701343159618277976427)
                      ·
                        rfl

theorem cell23_4718194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_4718194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718194 prefixEnd_4718194 := by exact prefixLift 4718194
  have htrace : WordTrace (prefixWord ++ tailWord_4718194) baseStart_4718194 baseEnd_4718194 := by
    simpa [prefixWord, tailWord_4718194, baseEnd_4718194] using wordTrace_append hprefix tailTrace_4718194
  have hstable : (prefixWord ++ tailWord_4718194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718194).length < 2 ^ (prefixWord ++ tailWord_4718194).sum := by decide
  have hdescent : baseEnd_4718194 < baseStart_4718194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718223 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_4718223 : Nat := 118140960795 + 4718223 * 2 ^ 59
def prefixEnd_4718223 : Nat := 4983230072969 + 3 ^ 40 * 4718223 * 2
def baseEnd_4718223 : Nat := 2422716234098598664513793

theorem tailTrace_4718223 : CollatzResearch.WordTrace tailWord_4718223 prefixEnd_4718223 2422716234098598664513793 := by
  unfold tailWord_4718223
  simp only [CollatzResearch.WordTrace]
  refine ⟨172087730385691354179831323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114725153590460902786554215 172087730385691354179831323)
  ·
    refine ⟨258131595578537031269746985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172087730385691354179831323 258131595578537031269746985)
    ·
      refine ⟨193598696683902773452310239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258131595578537031269746985 193598696683902773452310239)
      ·
        refine ⟨290398045025854160178465359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193598696683902773452310239 290398045025854160178465359)
        ·
          refine ⟨435597067538781240267698039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290398045025854160178465359 435597067538781240267698039)
          ·
            refine ⟨653395601308171860401547059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435597067538781240267698039 653395601308171860401547059)
            ·
              refine ⟨980093401962257790602320589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653395601308171860401547059 980093401962257790602320589)
              ·
                refine ⟨367535025735846671475870221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 980093401962257790602320589 367535025735846671475870221)
                ·
                  refine ⟨137825634650942501803451333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367535025735846671475870221 137825634650942501803451333)
                  ·
                    refine ⟨25842306497051719088147125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137825634650942501803451333 25842306497051719088147125)
                    ·
                      refine ⟨2422716234098598664513793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25842306497051719088147125 2422716234098598664513793)
                      ·
                        rfl

theorem cell23_4718223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_4718223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718223 prefixEnd_4718223 := by exact prefixLift 4718223
  have htrace : WordTrace (prefixWord ++ tailWord_4718223) baseStart_4718223 baseEnd_4718223 := by
    simpa [prefixWord, tailWord_4718223, baseEnd_4718223] using wordTrace_append hprefix tailTrace_4718223
  have hstable : (prefixWord ++ tailWord_4718223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718223).length < 2 ^ (prefixWord ++ tailWord_4718223).sum := by decide
  have hdescent : baseEnd_4718223 < baseStart_4718223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718233 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_4718233 : Nat := 118140960795 + 4718233 * 2 ^ 59
def prefixEnd_4718233 : Nat := 4983230072969 + 3 ^ 40 * 4718233 * 2
def baseEnd_4718233 : Nat := 2422721368905143625388747

theorem tailTrace_4718233 : CollatzResearch.WordTrace tailWord_4718233 prefixEnd_4718233 2422721368905143625388747 := by
  unfold tailWord_4718233
  simp only [CollatzResearch.WordTrace]
  refine ⟨172088095115655125887695353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114725396743770083925130235 172088095115655125887695353)
  ·
    refine ⟨129066071336741344415771515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172088095115655125887695353 129066071336741344415771515)
    ·
      refine ⟨193599107005112016623657273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129066071336741344415771515 193599107005112016623657273)
      ·
        refine ⟨145199330253834012467742955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193599107005112016623657273 145199330253834012467742955)
        ·
          refine ⟨217798995380751018701614433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145199330253834012467742955 217798995380751018701614433)
          ·
            refine ⟨163349246535563264026210825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217798995380751018701614433 163349246535563264026210825)
            ·
              refine ⟨122511934901672448019658119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163349246535563264026210825 122511934901672448019658119)
              ·
                refine ⟨183767902352508672029487179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122511934901672448019658119 183767902352508672029487179)
                ·
                  refine ⟨275651853528763008044230769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183767902352508672029487179 275651853528763008044230769)
                  ·
                    refine ⟨206738890146572256033173077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 275651853528763008044230769 206738890146572256033173077)
                    ·
                      refine ⟨2422721368905143625388747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 206738890146572256033173077 2422721368905143625388747)
                      ·
                        rfl

theorem cell23_4718233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_4718233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718233 prefixEnd_4718233 := by exact prefixLift 4718233
  have htrace : WordTrace (prefixWord ++ tailWord_4718233) baseStart_4718233 baseEnd_4718233 := by
    simpa [prefixWord, tailWord_4718233, baseEnd_4718233] using wordTrace_append hprefix tailTrace_4718233
  have hstable : (prefixWord ++ tailWord_4718233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718233).length < 2 ^ (prefixWord ++ tailWord_4718233).sum := by decide
  have hdescent : baseEnd_4718233 < baseStart_4718233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718240 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_4718240 : Nat := 118140960795 + 4718240 * 2 ^ 59
def prefixEnd_4718240 : Nat := 4983230072969 + 3 ^ 40 * 4718240 * 2
def baseEnd_4718240 : Nat := 2422724963269725098001215

theorem tailTrace_4718240 : CollatzResearch.WordTrace tailWord_4718240 prefixEnd_4718240 2422724963269725098001215 := by
  unfold tailWord_4718240
  simp only [CollatzResearch.WordTrace]
  refine ⟨86044175213314883041600087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114725566951086510722133449 86044175213314883041600087)
  ·
    refine ⟨129066262819972324562400131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86044175213314883041600087 129066262819972324562400131)
    ·
      refine ⟨193599394229958486843600197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129066262819972324562400131 193599394229958486843600197)
      ·
        refine ⟨36299886418117216283175037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193599394229958486843600197 36299886418117216283175037)
        ·
          refine ⟨13612457406793956106190639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36299886418117216283175037 13612457406793956106190639)
          ·
            refine ⟨20418686110190934159285959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13612457406793956106190639 20418686110190934159285959)
            ·
              refine ⟨30628029165286401238928939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20418686110190934159285959 30628029165286401238928939)
              ·
                refine ⟨45942043747929601858393409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30628029165286401238928939 45942043747929601858393409)
                ·
                  refine ⟨34456532810947201393795057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45942043747929601858393409 34456532810947201393795057)
                  ·
                    refine ⟨25842399608210401045346293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34456532810947201393795057 25842399608210401045346293)
                    ·
                      refine ⟨2422724963269725098001215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25842399608210401045346293 2422724963269725098001215)
                      ·
                        rfl

theorem cell23_4718240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_4718240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718240 prefixEnd_4718240 := by exact prefixLift 4718240
  have htrace : WordTrace (prefixWord ++ tailWord_4718240) baseStart_4718240 baseEnd_4718240 := by
    simpa [prefixWord, tailWord_4718240, baseEnd_4718240] using wordTrace_append hprefix tailTrace_4718240
  have hstable : (prefixWord ++ tailWord_4718240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718240).length < 2 ^ (prefixWord ++ tailWord_4718240).sum := by decide
  have hdescent : baseEnd_4718240 < baseStart_4718240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718262 : List Nat := [5, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_4718262 : Nat := 118140960795 + 4718262 * 2 ^ 59
def prefixEnd_4718262 : Nat := 4983230072969 + 3 ^ 40 * 4718262 * 2
def baseEnd_4718262 : Nat := 2422736259844124011926115

theorem tailTrace_4718262 : CollatzResearch.WordTrace tailWord_4718262 prefixEnd_4718262 2422736259844124011926115 := by
  unfold tailWord_4718262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10755572052034378990031315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114726101888366709227000693 10755572052034378990031315)
  ·
    refine ⟨16133358078051568485046973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10755572052034378990031315 16133358078051568485046973)
    ·
      refine ⟨6050009279269338181892615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16133358078051568485046973 6050009279269338181892615)
      ·
        refine ⟨9075013918904007272838923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050009279269338181892615 9075013918904007272838923)
        ·
          refine ⟨13612520878356010909258385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075013918904007272838923 13612520878356010909258385)
          ·
            refine ⟨10209390658767008181943789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13612520878356010909258385 10209390658767008181943789)
            ·
              refine ⟨3828521497037628068228921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10209390658767008181943789 3828521497037628068228921)
              ·
                refine ⟨2871391122778221051171691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828521497037628068228921 2871391122778221051171691)
                ·
                  refine ⟨4307086684167331576757537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871391122778221051171691 4307086684167331576757537)
                  ·
                    refine ⟨3230315013125498682568153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4307086684167331576757537 3230315013125498682568153)
                    ·
                      refine ⟨2422736259844124011926115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230315013125498682568153 2422736259844124011926115)
                      ·
                        rfl

theorem cell23_4718262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_4718262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718262 prefixEnd_4718262 := by exact prefixLift 4718262
  have htrace : WordTrace (prefixWord ++ tailWord_4718262) baseStart_4718262 baseEnd_4718262 := by
    simpa [prefixWord, tailWord_4718262, baseEnd_4718262] using wordTrace_append hprefix tailTrace_4718262
  have hstable : (prefixWord ++ tailWord_4718262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718262).length < 2 ^ (prefixWord ++ tailWord_4718262).sum := by decide
  have hdescent : baseEnd_4718262 < baseStart_4718262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718280 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_4718280 : Nat := 118140960795 + 4718280 * 2 ^ 59
def prefixEnd_4718280 : Nat := 4983230072969 + 3 ^ 40 * 4718280 * 2
def baseEnd_4718280 : Nat := 2422745502495904941501031

theorem tailTrace_4718280 : CollatzResearch.WordTrace tailWord_4718280 prefixEnd_4718280 2422745502495904941501031 := by
  unfold tailWord_4718280
  simp only [CollatzResearch.WordTrace]
  refine ⟨86044904673242426457328147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114726539564323235276437529 86044904673242426457328147)
  ·
    refine ⟨129067357009863639685992221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86044904673242426457328147 129067357009863639685992221)
    ·
      refine ⟨48400258878698864882247083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129067357009863639685992221 48400258878698864882247083)
      ·
        refine ⟨72600388318048297323370625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48400258878698864882247083 72600388318048297323370625)
        ·
          refine ⟨54450291238536222992527969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72600388318048297323370625 54450291238536222992527969)
          ·
            refine ⟨40837718428902167244395977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54450291238536222992527969 40837718428902167244395977)
            ·
              refine ⟨30628288821676625433296983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40837718428902167244395977 30628288821676625433296983)
              ·
                refine ⟨45942433232514938149945475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30628288821676625433296983 45942433232514938149945475)
                ·
                  refine ⟨68913649848772407224918213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45942433232514938149945475 68913649848772407224918213)
                  ·
                    refine ⟨12921309346644826354672165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68913649848772407224918213 12921309346644826354672165)
                    ·
                      refine ⟨2422745502495904941501031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12921309346644826354672165 2422745502495904941501031)
                      ·
                        rfl

theorem cell23_4718280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_4718280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718280 prefixEnd_4718280 := by exact prefixLift 4718280
  have htrace : WordTrace (prefixWord ++ tailWord_4718280) baseStart_4718280 baseEnd_4718280 := by
    simpa [prefixWord, tailWord_4718280, baseEnd_4718280] using wordTrace_append hprefix tailTrace_4718280
  have hstable : (prefixWord ++ tailWord_4718280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718280).length < 2 ^ (prefixWord ++ tailWord_4718280).sum := by decide
  have hdescent : baseEnd_4718280 < baseStart_4718280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718320 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 4, 5]
def baseStart_4718320 : Nat := 118140960795 + 4718320 * 2 ^ 59
def prefixEnd_4718320 : Nat := 4983230072969 + 3 ^ 40 * 4718320 * 2
def baseEnd_4718320 : Nat := 807588680574028261666949

theorem tailTrace_4718320 : CollatzResearch.WordTrace tailWord_4718320 prefixEnd_4718320 807588680574028261666949 := by
  unfold tailWord_4718320
  simp only [CollatzResearch.WordTrace]
  refine ⟨86045634133169969873056207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114727512177559959830741609 86045634133169969873056207)
  ·
    refine ⟨129068451199754954809584311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86045634133169969873056207 129068451199754954809584311)
    ·
      refine ⟨193602676799632432214376467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129068451199754954809584311 193602676799632432214376467)
      ·
        refine ⟨290404015199448648321564701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193602676799632432214376467 290404015199448648321564701)
        ·
          refine ⟨108901505699793243120586763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290404015199448648321564701 108901505699793243120586763)
          ·
            refine ⟨163352258549689864680880145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108901505699793243120586763 163352258549689864680880145)
            ·
              refine ⟨122514193912267398510660109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163352258549689864680880145 122514193912267398510660109)
              ·
                refine ⟨45942822717100274441497541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122514193912267398510660109 45942822717100274441497541)
                ·
                  refine ⟨8614279259456301457780789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45942822717100274441497541 8614279259456301457780789)
                  ·
                    refine ⟨807588680574028261666949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8614279259456301457780789 807588680574028261666949)
                    ·
                      rfl

theorem cell23_4718320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_4718320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718320 prefixEnd_4718320 := by exact prefixLift 4718320
  have htrace : WordTrace (prefixWord ++ tailWord_4718320) baseStart_4718320 baseEnd_4718320 := by
    simpa [prefixWord, tailWord_4718320, baseEnd_4718320] using wordTrace_append hprefix tailTrace_4718320
  have hstable : (prefixWord ++ tailWord_4718320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718320).length < 2 ^ (prefixWord ++ tailWord_4718320).sum := by decide
  have hdescent : baseEnd_4718320 < baseStart_4718320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718327 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 2, 5, 2]
def baseStart_4718327 : Nat := 118140960795 + 4718327 * 2 ^ 59
def prefixEnd_4718327 : Nat := 4983230072969 + 3 ^ 40 * 4718327 * 2
def baseEnd_4718327 : Nat := 2422769636086666257613315

theorem tailTrace_4718327 : CollatzResearch.WordTrace tailWord_4718327 prefixEnd_4718327 2422769636086666257613315 := by
  unfold tailWord_4718327
  simp only [CollatzResearch.WordTrace]
  refine ⟨172091523577314579941617235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114727682384876386627744823 172091523577314579941617235)
  ·
    refine ⟨258137285365971869912425853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172091523577314579941617235 258137285365971869912425853)
    ·
      refine ⟨96801482012239451217159695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258137285365971869912425853 96801482012239451217159695)
      ·
        refine ⟨145202223018359176825739543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96801482012239451217159695 145202223018359176825739543)
        ·
          refine ⟨217803334527538765238609315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145202223018359176825739543 217803334527538765238609315)
          ·
            refine ⟨326705001791308147857913973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217803334527538765238609315 326705001791308147857913973)
            ·
              refine ⟨30628593917935138861679435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 326705001791308147857913973 30628593917935138861679435)
              ·
                refine ⟨45942890876902708292519153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30628593917935138861679435 45942890876902708292519153)
                ·
                  refine ⟨34457168157677031219389365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45942890876902708292519153 34457168157677031219389365)
                  ·
                    refine ⟨3230359514782221676817753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34457168157677031219389365 3230359514782221676817753)
                    ·
                      refine ⟨2422769636086666257613315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230359514782221676817753 2422769636086666257613315)
                      ·
                        rfl

theorem cell23_4718327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_4718327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718327 prefixEnd_4718327 := by exact prefixLift 4718327
  have htrace : WordTrace (prefixWord ++ tailWord_4718327) baseStart_4718327 baseEnd_4718327 := by
    simpa [prefixWord, tailWord_4718327, baseEnd_4718327] using wordTrace_append hprefix tailTrace_4718327
  have hstable : (prefixWord ++ tailWord_4718327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718327).length < 2 ^ (prefixWord ++ tailWord_4718327).sum := by decide
  have hdescent : baseEnd_4718327 < baseStart_4718327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718354 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4718354 : Nat := 118140960795 + 4718354 * 2 ^ 59
def prefixEnd_4718354 : Nat := 4983230072969 + 3 ^ 40 * 4718354 * 2
def baseEnd_4718354 : Nat := 807594500021445883991897

theorem tailTrace_4718354 : CollatzResearch.WordTrace tailWord_4718354 prefixEnd_4718354 807594500021445883991897 := by
  unfold tailWord_4718354
  simp only [CollatzResearch.WordTrace]
  refine ⟨43023127087054190888212529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114728338898811175701900077 43023127087054190888212529)
  ·
    refine ⟨32267345315290643166159397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43023127087054190888212529 32267345315290643166159397)
    ·
      refine ⟨6050127246616995593654887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32267345315290643166159397 6050127246616995593654887)
      ·
        refine ⟨9075190869925493390482331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050127246616995593654887 9075190869925493390482331)
        ·
          refine ⟨13612786304888240085723497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075190869925493390482331 13612786304888240085723497)
          ·
            refine ⟨10209589728666180064292623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13612786304888240085723497 10209589728666180064292623)
            ·
              refine ⟨15314384592999270096438935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10209589728666180064292623 15314384592999270096438935)
              ·
                refine ⟨22971576889498905144658403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15314384592999270096438935 22971576889498905144658403)
                ·
                  refine ⟨34457365334248357716987605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22971576889498905144658403 34457365334248357716987605)
                  ·
                    refine ⟨807594500021445883991897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34457365334248357716987605 807594500021445883991897)
                    ·
                      rfl

theorem cell23_4718354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4718354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718354 prefixEnd_4718354 := by exact prefixLift 4718354
  have htrace : WordTrace (prefixWord ++ tailWord_4718354) baseStart_4718354 baseEnd_4718354 := by
    simpa [prefixWord, tailWord_4718354, baseEnd_4718354] using wordTrace_append hprefix tailTrace_4718354
  have hstable : (prefixWord ++ tailWord_4718354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718354).length < 2 ^ (prefixWord ++ tailWord_4718354).sum := by decide
  have hdescent : baseEnd_4718354 < baseStart_4718354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718357 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_4718357 : Nat := 118140960795 + 4718357 * 2 ^ 59
def prefixEnd_4718357 : Nat := 4983230072969 + 3 ^ 40 * 4718357 * 2
def baseEnd_4718357 : Nat := 2422785040506301140238177

theorem tailTrace_4718357 : CollatzResearch.WordTrace tailWord_4718357 prefixEnd_4718357 2422785040506301140238177 := by
  unfold tailWord_4718357
  simp only [CollatzResearch.WordTrace]
  refine ⟨172092617767205895065209325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114728411844803930043472883 172092617767205895065209325)
  ·
    refine ⟨64534731662702210649453497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172092617767205895065209325 64534731662702210649453497)
    ·
      refine ⟨48401048747026657987090123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64534731662702210649453497 48401048747026657987090123)
      ·
        refine ⟨72601573120539986980635185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48401048747026657987090123 72601573120539986980635185)
        ·
          refine ⟨54451179840404990235476389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72601573120539986980635185 54451179840404990235476389)
          ·
            refine ⟨10209596220075935669151823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54451179840404990235476389 10209596220075935669151823)
            ·
              refine ⟨15314394330113903503727735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10209596220075935669151823 15314394330113903503727735)
              ·
                refine ⟨22971591495170855255591603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15314394330113903503727735 22971591495170855255591603)
                ·
                  refine ⟨34457387242756282883387405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22971591495170855255591603 34457387242756282883387405)
                  ·
                    refine ⟨12921520216033606081270277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34457387242756282883387405 12921520216033606081270277)
                    ·
                      refine ⟨2422785040506301140238177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12921520216033606081270277 2422785040506301140238177)
                      ·
                        rfl

theorem cell23_4718357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_4718357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718357 prefixEnd_4718357 := by exact prefixLift 4718357
  have htrace : WordTrace (prefixWord ++ tailWord_4718357) baseStart_4718357 baseEnd_4718357 := by
    simpa [prefixWord, tailWord_4718357, baseEnd_4718357] using wordTrace_append hprefix tailTrace_4718357
  have hstable : (prefixWord ++ tailWord_4718357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718357).length < 2 ^ (prefixWord ++ tailWord_4718357).sum := by decide
  have hdescent : baseEnd_4718357 < baseStart_4718357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718367 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 5, 4]
def baseStart_4718367 : Nat := 118140960795 + 4718367 * 2 ^ 59
def prefixEnd_4718367 : Nat := 4983230072969 + 3 ^ 40 * 4718367 * 2
def baseEnd_4718367 : Nat := 807596725104282033704377

theorem tailTrace_4718367 : CollatzResearch.WordTrace tailWord_4718367 prefixEnd_4718367 807596725104282033704377 := by
  unfold tailWord_4718367
  simp only [CollatzResearch.WordTrace]
  refine ⟨172092982497169666773073355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114728654998113111182048903 172092982497169666773073355)
  ·
    refine ⟨258139473745754500159610033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172092982497169666773073355 258139473745754500159610033)
    ·
      refine ⟨193604605309315875119707525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258139473745754500159610033 193604605309315875119707525)
      ·
        refine ⟨36300863495496726584945161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193604605309315875119707525 36300863495496726584945161)
        ·
          refine ⟨27225647621622544938708871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36300863495496726584945161 27225647621622544938708871)
          ·
            refine ⟨40838471432433817408063307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27225647621622544938708871 40838471432433817408063307)
            ·
              refine ⟨61257707148650726112094961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40838471432433817408063307 61257707148650726112094961)
              ·
                refine ⟨45943280361488044584071221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61257707148650726112094961 45943280361488044584071221)
                ·
                  refine ⟨4307182533889504179756677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45943280361488044584071221 4307182533889504179756677)
                  ·
                    refine ⟨807596725104282033704377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307182533889504179756677 807596725104282033704377)
                    ·
                      rfl

theorem cell23_4718367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_4718367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718367 prefixEnd_4718367 := by exact prefixLift 4718367
  have htrace : WordTrace (prefixWord ++ tailWord_4718367) baseStart_4718367 baseEnd_4718367 := by
    simpa [prefixWord, tailWord_4718367, baseEnd_4718367] using wordTrace_append hprefix tailTrace_4718367
  have hstable : (prefixWord ++ tailWord_4718367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718367).length < 2 ^ (prefixWord ++ tailWord_4718367).sum := by decide
  have hdescent : baseEnd_4718367 < baseStart_4718367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718418 : List Nat := [3, 2, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_4718418 : Nat := 118140960795 + 4718418 * 2 ^ 59
def prefixEnd_4718418 : Nat := 4983230072969 + 3 ^ 40 * 4718418 * 2
def baseEnd_4718418 : Nat := 807605454275408467191799

theorem tailTrace_4718418 : CollatzResearch.WordTrace tailWord_4718418 prefixEnd_4718418 807605454275408467191799 := by
  unfold tailWord_4718418
  simp only [CollatzResearch.WordTrace]
  refine ⟨43023710654996225620794977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114729895079989934988786605 43023710654996225620794977)
  ·
    refine ⟨32267782991247169215596233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43023710654996225620794977 32267782991247169215596233)
    ·
      refine ⟨24200837243435376911697175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32267782991247169215596233 24200837243435376911697175)
      ·
        refine ⟨36301255865153065367545763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24200837243435376911697175 36301255865153065367545763)
        ·
          refine ⟨54451883797729598051318645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36301255865153065367545763 54451883797729598051318645)
          ·
            refine ⟨5104864106037149817311123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54451883797729598051318645 5104864106037149817311123)
            ·
              refine ⟨7657296159055724725966685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5104864106037149817311123 7657296159055724725966685)
              ·
                refine ⟨2871486059645896772237507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7657296159055724725966685 2871486059645896772237507)
                ·
                  refine ⟨4307229089468845158356261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871486059645896772237507 4307229089468845158356261)
                  ·
                    refine ⟨807605454275408467191799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307229089468845158356261 807605454275408467191799)
                    ·
                      rfl

theorem cell23_4718418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_4718418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718418 prefixEnd_4718418 := by exact prefixLift 4718418
  have htrace : WordTrace (prefixWord ++ tailWord_4718418) baseStart_4718418 baseEnd_4718418 := by
    simpa [prefixWord, tailWord_4718418, baseEnd_4718418] using wordTrace_append hprefix tailTrace_4718418
  have hstable : (prefixWord ++ tailWord_4718418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718418).length < 2 ^ (prefixWord ++ tailWord_4718418).sum := by decide
  have hdescent : baseEnd_4718418 < baseStart_4718418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718441 : List Nat := [1, 2, 1, 1, 1, 3, 1, 8, 1, 1, 3]
def baseStart_4718441 : Nat := 118140960795 + 4718441 * 2 ^ 59
def prefixEnd_4718441 : Nat := 4983230072969 + 3 ^ 40 * 4718441 * 2
def baseEnd_4718441 : Nat := 2422828172881278811587791

theorem tailTrace_4718441 : CollatzResearch.WordTrace tailWord_4718441 prefixEnd_4718441 2422828172881278811587791 := by
  unfold tailWord_4718441
  simp only [CollatzResearch.WordTrace]
  refine ⟨172095681498901577411267177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114730454332601051607511451 172095681498901577411267177)
  ·
    refine ⟨129071761124176183058450383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172095681498901577411267177 129071761124176183058450383)
    ·
      refine ⟨193607641686264274587675575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129071761124176183058450383 193607641686264274587675575)
      ·
        refine ⟨290411462529396411881513363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193607641686264274587675575 290411462529396411881513363)
        ·
          refine ⟨435617193794094617822270045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290411462529396411881513363 435617193794094617822270045)
          ·
            refine ⟨163356447672785481683351267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 435617193794094617822270045 163356447672785481683351267)
            ·
              refine ⟨245034671509178222525026901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163356447672785481683351267 245034671509178222525026901)
              ·
                refine ⟨2871500056748182295215159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 245034671509178222525026901 2871500056748182295215159)
                ·
                  refine ⟨4307250085122273442822739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871500056748182295215159 4307250085122273442822739)
                  ·
                    refine ⟨6460875127683410164234109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4307250085122273442822739 6460875127683410164234109)
                    ·
                      refine ⟨2422828172881278811587791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6460875127683410164234109 2422828172881278811587791)
                      ·
                        rfl

theorem cell23_4718441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 1, 3].length) (baseStart_4718441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718441 prefixEnd_4718441 := by exact prefixLift 4718441
  have htrace : WordTrace (prefixWord ++ tailWord_4718441) baseStart_4718441 baseEnd_4718441 := by
    simpa [prefixWord, tailWord_4718441, baseEnd_4718441] using wordTrace_append hprefix tailTrace_4718441
  have hstable : (prefixWord ++ tailWord_4718441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718441).length < 2 ^ (prefixWord ++ tailWord_4718441).sum := by decide
  have hdescent : baseEnd_4718441 < baseStart_4718441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718457 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 1, 6]
def baseStart_4718457 : Nat := 118140960795 + 4718457 * 2 ^ 59
def prefixEnd_4718457 : Nat := 4983230072969 + 3 ^ 40 * 4718457 * 2
def baseEnd_4718457 : Nat := 807612129523916916329239

theorem tailTrace_4718457 : CollatzResearch.WordTrace tailWord_4718457 prefixEnd_4718457 807612129523916916329239 := by
  unfold tailWord_4718457
  simp only [CollatzResearch.WordTrace]
  refine ⟨172096265066843612143849625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114730843377895741429233083 172096265066843612143849625)
  ·
    refine ⟨129072198800132709107887219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172096265066843612143849625 129072198800132709107887219)
    ·
      refine ⟨193608298200199063661830829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129072198800132709107887219 193608298200199063661830829)
      ·
        refine ⟨72603111825074648873186561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193608298200199063661830829 72603111825074648873186561)
        ·
          refine ⟨54452333868805986654889921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72603111825074648873186561 54452333868805986654889921)
          ·
            refine ⟨40839250401604489991167441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54452333868805986654889921 40839250401604489991167441)
            ·
              refine ⟨30629437801203367493375581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40839250401604489991167441 30629437801203367493375581)
              ·
                refine ⟨11486039175451262810015843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30629437801203367493375581 11486039175451262810015843)
                ·
                  refine ⟨17229058763176894215023765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11486039175451262810015843 17229058763176894215023765)
                  ·
                    refine ⟨807612129523916916329239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17229058763176894215023765 807612129523916916329239)
                    ·
                      rfl

theorem cell23_4718457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_4718457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718457 prefixEnd_4718457 := by exact prefixLift 4718457
  have htrace : WordTrace (prefixWord ++ tailWord_4718457) baseStart_4718457 baseEnd_4718457 := by
    simpa [prefixWord, tailWord_4718457, baseEnd_4718457] using wordTrace_append hprefix tailTrace_4718457
  have hstable : (prefixWord ++ tailWord_4718457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718457).length < 2 ^ (prefixWord ++ tailWord_4718457).sum := by decide
  have hdescent : baseEnd_4718457 < baseStart_4718457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718486 : List Nat := [5, 3, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4718486 : Nat := 118140960795 + 4718486 * 2 ^ 59
def prefixEnd_4718486 : Nat := 4983230072969 + 3 ^ 40 * 4718486 * 2
def baseEnd_4718486 : Nat := 807617093170243711841695

theorem tailTrace_4718486 : CollatzResearch.WordTrace tailWord_4718486 prefixEnd_4718486 807617093170243711841695 := by
  unfold tailWord_4718486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756082673983659381040957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114731548522492366731103541 10756082673983659381040957)
  ·
    refine ⟨4033531002743872267890359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10756082673983659381040957 4033531002743872267890359)
    ·
      refine ⟨6050296504115808401835539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033531002743872267890359 6050296504115808401835539)
      ·
        refine ⟨9075444756173712602753309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050296504115808401835539 9075444756173712602753309)
        ·
          refine ⟨3403291783565142226032491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9075444756173712602753309 3403291783565142226032491)
          ·
            refine ⟨5104937675347713339048737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403291783565142226032491 5104937675347713339048737)
            ·
              refine ⟨3828703256510785004286553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5104937675347713339048737 3828703256510785004286553)
              ·
                refine ⟨2871527442383088753214915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828703256510785004286553 2871527442383088753214915)
                ·
                  refine ⟨4307291163574633129822373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871527442383088753214915 4307291163574633129822373)
                  ·
                    refine ⟨807617093170243711841695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307291163574633129822373 807617093170243711841695)
                    ·
                      rfl

theorem cell23_4718486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4718486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718486 prefixEnd_4718486 := by exact prefixLift 4718486
  have htrace : WordTrace (prefixWord ++ tailWord_4718486) baseStart_4718486 baseEnd_4718486 := by
    simpa [prefixWord, tailWord_4718486, baseEnd_4718486] using wordTrace_append hprefix tailTrace_4718486
  have hstable : (prefixWord ++ tailWord_4718486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718486).length < 2 ^ (prefixWord ++ tailWord_4718486).sum := by decide
  have hdescent : baseEnd_4718486 < baseStart_4718486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718492 : List Nat := [2, 2, 3, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4718492 : Nat := 118140960795 + 4718492 * 2 ^ 59
def prefixEnd_4718492 : Nat := 4983230072969 + 3 ^ 40 * 4718492 * 2
def baseEnd_4718492 : Nat := 2422854360394658112050057

theorem tailTrace_4718492 : CollatzResearch.WordTrace tailWord_4718492 prefixEnd_4718492 2422854360394658112050057 := by
  unfold tailWord_4718492
  simp only [CollatzResearch.WordTrace]
  refine ⟨86048770810858406560686865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114731694414477875414249153 86048770810858406560686865)
  ·
    refine ⟨64536578108143804920515149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86048770810858406560686865 64536578108143804920515149)
    ·
      refine ⟨24201216790553926845193181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64536578108143804920515149 24201216790553926845193181)
      ·
        refine ⟨9075456296457722566947443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24201216790553926845193181 9075456296457722566947443)
        ·
          refine ⟨13613184444686583850421165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075456296457722566947443 13613184444686583850421165)
          ·
            refine ⟨5104944166757468943907937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13613184444686583850421165 5104944166757468943907937)
            ·
              refine ⟨3828708125068101707930953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5104944166757468943907937 3828708125068101707930953)
              ·
                refine ⟨2871531093801076280948215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828708125068101707930953 2871531093801076280948215)
                ·
                  refine ⟨4307296640701614421422323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871531093801076280948215 4307296640701614421422323)
                  ·
                    refine ⟨6460944961052421632133485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4307296640701614421422323 6460944961052421632133485)
                    ·
                      refine ⟨2422854360394658112050057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6460944961052421632133485 2422854360394658112050057)
                      ·
                        rfl

theorem cell23_4718492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4718492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718492 prefixEnd_4718492 := by exact prefixLift 4718492
  have htrace : WordTrace (prefixWord ++ tailWord_4718492) baseStart_4718492 baseEnd_4718492 := by
    simpa [prefixWord, tailWord_4718492, baseEnd_4718492] using wordTrace_append hprefix tailTrace_4718492
  have hstable : (prefixWord ++ tailWord_4718492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718492).length < 2 ^ (prefixWord ++ tailWord_4718492).sum := by decide
  have hdescent : baseEnd_4718492 < baseStart_4718492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718527 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_4718527 : Nat := 118140960795 + 4718527 * 2 ^ 59
def prefixEnd_4718527 : Nat := 4983230072969 + 3 ^ 40 * 4718527 * 2
def baseEnd_4718527 : Nat := 2422872332217565475112395

theorem tailTrace_4718527 : CollatzResearch.WordTrace tailWord_4718527 prefixEnd_4718527 2422872332217565475112395 := by
  unfold tailWord_4718527
  simp only [CollatzResearch.WordTrace]
  refine ⟨172098818176590014098897835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114732545451060009399265223 172098818176590014098897835)
  ·
    refine ⟨258148227264885021148346753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172098818176590014098897835 258148227264885021148346753)
    ·
      refine ⟨193611170448663765861260065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258148227264885021148346753 193611170448663765861260065)
      ·
        refine ⟨145208377836497824395945049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193611170448663765861260065 145208377836497824395945049)
        ·
          refine ⟨108906283377373368296958787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145208377836497824395945049 108906283377373368296958787)
          ·
            refine ⟨163359425066060052445438181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108906283377373368296958787 163359425066060052445438181)
            ·
              refine ⟨30629892199886259833519659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163359425066060052445438181 30629892199886259833519659)
              ·
                refine ⟨45944838299829389750279489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30629892199886259833519659 45944838299829389750279489)
                ·
                  refine ⟨34458628724872042312709617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45944838299829389750279489 34458628724872042312709617)
                  ·
                    refine ⟨25843971543654031734532213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34458628724872042312709617 25843971543654031734532213)
                    ·
                      refine ⟨2422872332217565475112395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25843971543654031734532213 2422872332217565475112395)
                      ·
                        rfl

theorem cell23_4718527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_4718527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718527 prefixEnd_4718527 := by exact prefixLift 4718527
  have htrace : WordTrace (prefixWord ++ tailWord_4718527) baseStart_4718527 baseEnd_4718527 := by
    simpa [prefixWord, tailWord_4718527, baseEnd_4718527] using wordTrace_append hprefix tailTrace_4718527
  have hstable : (prefixWord ++ tailWord_4718527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718527).length < 2 ^ (prefixWord ++ tailWord_4718527).sum := by decide
  have hdescent : baseEnd_4718527 < baseStart_4718527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718537 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_4718537 : Nat := 118140960795 + 4718537 * 2 ^ 59
def prefixEnd_4718537 : Nat := 4983230072969 + 3 ^ 40 * 4718537 * 2
def baseEnd_4718537 : Nat := 2422877467024110435987349

theorem tailTrace_4718537 : CollatzResearch.WordTrace tailWord_4718537 prefixEnd_4718537 2422877467024110435987349 := by
  unfold tailWord_4718537
  simp only [CollatzResearch.WordTrace]
  refine ⟨172099182906553785806761865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114732788604369190537841243 172099182906553785806761865)
  ·
    refine ⟨129074387179915339355071399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172099182906553785806761865 129074387179915339355071399)
    ·
      refine ⟨193611580769873009032607099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129074387179915339355071399 193611580769873009032607099)
      ·
        refine ⟨290417371154809513548910649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193611580769873009032607099 290417371154809513548910649)
        ·
          refine ⟨217813028366107135161682987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290417371154809513548910649 217813028366107135161682987)
          ·
            refine ⟨326719542549160702742524481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217813028366107135161682987 326719542549160702742524481)
            ·
              refine ⟨245039656911870527056893361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326719542549160702742524481 245039656911870527056893361)
              ·
                refine ⟨183779742683902895292670021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245039656911870527056893361 183779742683902895292670021)
                ·
                  refine ⟨34458701753231792867375629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183779742683902895292670021 34458701753231792867375629)
                  ·
                    refine ⟨12922013157461922325265861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34458701753231792867375629 12922013157461922325265861)
                    ·
                      refine ⟨2422877467024110435987349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12922013157461922325265861 2422877467024110435987349)
                      ·
                        rfl

theorem cell23_4718537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_4718537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718537 prefixEnd_4718537 := by exact prefixLift 4718537
  have htrace : WordTrace (prefixWord ++ tailWord_4718537) baseStart_4718537 baseEnd_4718537 := by
    simpa [prefixWord, tailWord_4718537, baseEnd_4718537] using wordTrace_append hprefix tailTrace_4718537
  have hstable : (prefixWord ++ tailWord_4718537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718537).length < 2 ^ (prefixWord ++ tailWord_4718537).sum := by decide
  have hdescent : baseEnd_4718537 < baseStart_4718537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718641 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 2, 5]
def baseStart_4718641 : Nat := 118140960795 + 4718641 * 2 ^ 59
def prefixEnd_4718641 : Nat := 4983230072969 + 3 ^ 40 * 4718641 * 2
def baseEnd_4718641 : Nat := 807643623004059343028957

theorem tailTrace_4718641 : CollatzResearch.WordTrace tailWord_4718641 prefixEnd_4718641 807643623004059343028957 := by
  unfold tailWord_4718641
  simp only [CollatzResearch.WordTrace]
  refine ⟨172102976098177011568547777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114735317398784674379031851 172102976098177011568547777)
  ·
    refine ⟨129077232073632758676410833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172102976098177011568547777 129077232073632758676410833)
    ·
      refine ⟨96807924055224569007308125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129077232073632758676410833 96807924055224569007308125)
      ·
        refine ⟨36302971520709213377740547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96807924055224569007308125 36302971520709213377740547)
        ·
          refine ⟨54454457281063820066610821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36302971520709213377740547 54454457281063820066610821)
          ·
            refine ⟨10210210740199466262489529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54454457281063820066610821 10210210740199466262489529)
            ·
              refine ⟨7657658055149599696867147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10210210740199466262489529 7657658055149599696867147)
              ·
                refine ⟨11486487082724399545300721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7657658055149599696867147 11486487082724399545300721)
                ·
                  refine ⟨8614865312043299658975541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11486487082724399545300721 8614865312043299658975541)
                  ·
                    refine ⟨807643623004059343028957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8614865312043299658975541 807643623004059343028957)
                    ·
                      rfl

theorem cell23_4718641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_4718641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718641 prefixEnd_4718641 := by exact prefixLift 4718641
  have htrace : WordTrace (prefixWord ++ tailWord_4718641) baseStart_4718641 baseEnd_4718641 := by
    simpa [prefixWord, tailWord_4718641, baseEnd_4718641] using wordTrace_append hprefix tailTrace_4718641
  have hstable : (prefixWord ++ tailWord_4718641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718641).length < 2 ^ (prefixWord ++ tailWord_4718641).sum := by decide
  have hdescent : baseEnd_4718641 < baseStart_4718641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718661 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 2, 4, 2]
def baseStart_4718661 : Nat := 118140960795 + 4718661 * 2 ^ 59
def prefixEnd_4718661 : Nat := 4983230072969 + 3 ^ 40 * 4718661 * 2
def baseEnd_4718661 : Nat := 2422941138625267950836779

theorem tailTrace_4718661 : CollatzResearch.WordTrace tailWord_4718661 prefixEnd_4718661 2422941138625267950836779 := by
  unfold tailWord_4718661
  simp only [CollatzResearch.WordTrace]
  refine ⟨172103705558104554984275837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114735803705403036656183891 172103705558104554984275837)
  ·
    refine ⟨64538889584289208119103439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172103705558104554984275837 64538889584289208119103439)
    ·
      refine ⟨96808334376433812178655159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64538889584289208119103439 96808334376433812178655159)
      ·
        refine ⟨145212501564650718267982739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96808334376433812178655159 145212501564650718267982739)
        ·
          refine ⟨217818752346976077401974109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145212501564650718267982739 217818752346976077401974109)
          ·
            refine ⟨81682032130116029025740291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217818752346976077401974109 81682032130116029025740291)
            ·
              refine ⟨122523048195174043538610437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81682032130116029025740291 122523048195174043538610437)
              ·
                refine ⟨22973071536595133163489457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122523048195174043538610437 22973071536595133163489457)
                ·
                  refine ⟨17229803652446349872617093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22973071536595133163489457 17229803652446349872617093)
                  ·
                    refine ⟨3230588184833690601115705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17229803652446349872617093 3230588184833690601115705)
                    ·
                      refine ⟨2422941138625267950836779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230588184833690601115705 2422941138625267950836779)
                      ·
                        rfl

theorem cell23_4718661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_4718661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718661 prefixEnd_4718661 := by exact prefixLift 4718661
  have htrace : WordTrace (prefixWord ++ tailWord_4718661) baseStart_4718661 baseEnd_4718661 := by
    simpa [prefixWord, tailWord_4718661, baseEnd_4718661] using wordTrace_append hprefix tailTrace_4718661
  have hstable : (prefixWord ++ tailWord_4718661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718661).length < 2 ^ (prefixWord ++ tailWord_4718661).sum := by decide
  have hdescent : baseEnd_4718661 < baseStart_4718661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718698 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_4718698 : Nat := 118140960795 + 4718698 * 2 ^ 59
def prefixEnd_4718698 : Nat := 4983230072969 + 3 ^ 40 * 4718698 * 2
def baseEnd_4718698 : Nat := 2422960137409484306074109

theorem tailTrace_4718698 : CollatzResearch.WordTrace tailWord_4718698 prefixEnd_4718698 2422960137409484306074109 := by
  unfold tailWord_4718698
  simp only [CollatzResearch.WordTrace]
  refine ⟨43026263764742627575843187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114736703372647006868915165 43026263764742627575843187)
  ·
    refine ⟨64539395647113941363764781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43026263764742627575843187 64539395647113941363764781)
    ·
      refine ⟨24202273367667728011411793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64539395647113941363764781 24202273367667728011411793)
      ·
        refine ⟨18151705025750796008558845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24202273367667728011411793 18151705025750796008558845)
        ·
          refine ⟨6806889384656548503209567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18151705025750796008558845 6806889384656548503209567)
          ·
            refine ⟨10210334076984822754814351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6806889384656548503209567 10210334076984822754814351)
            ·
              refine ⟨15315501115477234132221527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10210334076984822754814351 15315501115477234132221527)
              ·
                refine ⟨22973251673215851198332291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15315501115477234132221527 22973251673215851198332291)
                ·
                  refine ⟨34459877509823776797498437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22973251673215851198332291 34459877509823776797498437)
                  ·
                    refine ⟨6461227033091958149530957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34459877509823776797498437 6461227033091958149530957)
                    ·
                      refine ⟨2422960137409484306074109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461227033091958149530957 2422960137409484306074109)
                      ·
                        rfl

theorem cell23_4718698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_4718698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718698 prefixEnd_4718698 := by exact prefixLift 4718698
  have htrace : WordTrace (prefixWord ++ tailWord_4718698) baseStart_4718698 baseEnd_4718698 := by
    simpa [prefixWord, tailWord_4718698, baseEnd_4718698] using wordTrace_append hprefix tailTrace_4718698
  have hstable : (prefixWord ++ tailWord_4718698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718698).length < 2 ^ (prefixWord ++ tailWord_4718698).sum := by decide
  have hdescent : baseEnd_4718698 < baseStart_4718698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718738 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_4718738 : Nat := 118140960795 + 4718738 * 2 ^ 59
def prefixEnd_4718738 : Nat := 4983230072969 + 3 ^ 40 * 4718738 * 2
def baseEnd_4718738 : Nat := 2422980676635664149573925

theorem tailTrace_4718738 : CollatzResearch.WordTrace tailWord_4718738 prefixEnd_4718738 2422980676635664149573925 := by
  unfold tailWord_4718738
  simp only [CollatzResearch.WordTrace]
  refine ⟨43026628494706399283707217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114737675985883731423219245 43026628494706399283707217)
  ·
    refine ⟨32269971371029799462780413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43026628494706399283707217 32269971371029799462780413)
    ·
      refine ⟨12101239264136174798542655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32269971371029799462780413 12101239264136174798542655)
      ·
        refine ⟨18151858896204262197813983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12101239264136174798542655 18151858896204262197813983)
        ·
          refine ⟨27227788344306393296720975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18151858896204262197813983 27227788344306393296720975)
          ·
            refine ⟨40841682516459589945081463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27227788344306393296720975 40841682516459589945081463)
            ·
              refine ⟨61262523774689384917622195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40841682516459589945081463 61262523774689384917622195)
              ·
                refine ⟨91893785662034077376433293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61262523774689384917622195 91893785662034077376433293)
                ·
                  refine ⟨34460169623262779016162485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91893785662034077376433293 34460169623262779016162485)
                  ·
                    refine ⟨3230640902180885532765233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34460169623262779016162485 3230640902180885532765233)
                    ·
                      refine ⟨2422980676635664149573925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230640902180885532765233 2422980676635664149573925)
                      ·
                        rfl

theorem cell23_4718738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_4718738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718738 prefixEnd_4718738 := by exact prefixLift 4718738
  have htrace : WordTrace (prefixWord ++ tailWord_4718738) baseStart_4718738 baseEnd_4718738 := by
    simpa [prefixWord, tailWord_4718738, baseEnd_4718738] using wordTrace_append hprefix tailTrace_4718738
  have hstable : (prefixWord ++ tailWord_4718738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718738).length < 2 ^ (prefixWord ++ tailWord_4718738).sum := by decide
  have hdescent : baseEnd_4718738 < baseStart_4718738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718748 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_4718748 : Nat := 118140960795 + 4718748 * 2 ^ 59
def prefixEnd_4718748 : Nat := 4983230072969 + 3 ^ 40 * 4718748 * 2
def baseEnd_4718748 : Nat := 807661937147403036816293

theorem tailTrace_4718748 : CollatzResearch.WordTrace tailWord_4718748 prefixEnd_4718748 807661937147403036816293 := by
  unfold tailWord_4718748
  simp only [CollatzResearch.WordTrace]
  refine ⟨86053439354394684421346449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114737919139192912561795265 86053439354394684421346449)
  ·
    refine ⟨64540079515796013316009837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86053439354394684421346449 64540079515796013316009837)
    ·
      refine ⟨24202529818423504993503689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64540079515796013316009837 24202529818423504993503689)
      ·
        refine ⟨18151897363817628745127767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24202529818423504993503689 18151897363817628745127767)
        ·
          refine ⟨27227846045726443117691651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18151897363817628745127767 27227846045726443117691651)
          ·
            refine ⟨40841769068589664676537477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27227846045726443117691651 40841769068589664676537477)
            ·
              refine ⟨7657831700360562126850777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40841769068589664676537477 7657831700360562126850777)
              ·
                refine ⟨5743373775270421595138083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7657831700360562126850777 5743373775270421595138083)
                ·
                  refine ⟨8615060662905632392707125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743373775270421595138083 8615060662905632392707125)
                  ·
                    refine ⟨807661937147403036816293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8615060662905632392707125 807661937147403036816293)
                    ·
                      rfl

theorem cell23_4718748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_4718748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718748 prefixEnd_4718748 := by exact prefixLift 4718748
  have htrace : WordTrace (prefixWord ++ tailWord_4718748) baseStart_4718748 baseEnd_4718748 := by
    simpa [prefixWord, tailWord_4718748, baseEnd_4718748] using wordTrace_append hprefix tailTrace_4718748
  have hstable : (prefixWord ++ tailWord_4718748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718748).length < 2 ^ (prefixWord ++ tailWord_4718748).sum := by decide
  have hdescent : baseEnd_4718748 < baseStart_4718748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718771 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 3]
def baseStart_4718771 : Nat := 118140960795 + 4718771 * 2 ^ 59
def prefixEnd_4718771 : Nat := 4983230072969 + 3 ^ 40 * 4718771 * 2
def baseEnd_4718771 : Nat := 2422997621497262520461273

theorem tailTrace_4718771 : CollatzResearch.WordTrace tailWord_4718771 prefixEnd_4718771 2422997621497262520461273 := by
  unfold tailWord_4718771
  simp only [CollatzResearch.WordTrace]
  refine ⟨172107717587706043770780167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114738478391804029180520111 172107717587706043770780167)
  ·
    refine ⟨258161576381559065656170251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172107717587706043770780167 258161576381559065656170251)
    ·
      refine ⟨387242364572338598484255377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258161576381559065656170251 387242364572338598484255377)
      ·
        refine ⟨290431773429253948863191533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387242364572338598484255377 290431773429253948863191533)
        ·
          refine ⟨108911915035970230823696825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290431773429253948863191533 108911915035970230823696825)
          ·
            refine ⟨81683936276977673117772619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108911915035970230823696825 81683936276977673117772619)
            ·
              refine ⟨122525904415466509676658929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81683936276977673117772619 122525904415466509676658929)
              ·
                refine ⟨91894428311599882257494197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122525904415466509676658929 91894428311599882257494197)
                ·
                  refine ⟨8615102654212488961640081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91894428311599882257494197 8615102654212488961640081)
                  ·
                    refine ⟨6461326990659366721230061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8615102654212488961640081 6461326990659366721230061)
                    ·
                      refine ⟨2422997621497262520461273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461326990659366721230061 2422997621497262520461273)
                      ·
                        rfl

theorem cell23_4718771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_4718771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718771 prefixEnd_4718771 := by exact prefixLift 4718771
  have htrace : WordTrace (prefixWord ++ tailWord_4718771) baseStart_4718771 baseEnd_4718771 := by
    simpa [prefixWord, tailWord_4718771, baseEnd_4718771] using wordTrace_append hprefix tailTrace_4718771
  have hstable : (prefixWord ++ tailWord_4718771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718771).length < 2 ^ (prefixWord ++ tailWord_4718771).sum := by decide
  have hdescent : baseEnd_4718771 < baseStart_4718771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718788 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4718788 : Nat := 118140960795 + 4718788 * 2 ^ 59
def prefixEnd_4718788 : Nat := 4983230072969 + 3 ^ 40 * 4718788 * 2
def baseEnd_4718788 : Nat := 2423006350668388953948695

theorem tailTrace_4718788 : CollatzResearch.WordTrace tailWord_4718788 prefixEnd_4718788 2423006350668388953948695 := by
  unfold tailWord_4718788
  simp only [CollatzResearch.WordTrace]
  refine ⟨86054168814322227837074509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114738891752429637116099345 86054168814322227837074509)
  ·
    refine ⟨32270313305370835438902941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86054168814322227837074509 32270313305370835438902941)
    ·
      refine ⟨12101367489514063289588603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32270313305370835438902941 12101367489514063289588603)
      ·
        refine ⟨18152051234271094934382905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12101367489514063289588603 18152051234271094934382905)
        ·
          refine ⟨13614038425703321200787179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18152051234271094934382905 13614038425703321200787179)
          ·
            refine ⟨20421057638554981801180769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13614038425703321200787179 20421057638554981801180769)
            ·
              refine ⟨15315793228916236350885577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20421057638554981801180769 15315793228916236350885577)
              ·
                refine ⟨11486844921687177263164183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15315793228916236350885577 11486844921687177263164183)
                ·
                  refine ⟨17230267382530765894746275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11486844921687177263164183 17230267382530765894746275)
                  ·
                    refine ⟨25845401073796148842119413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17230267382530765894746275 25845401073796148842119413)
                    ·
                      refine ⟨2423006350668388953948695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25845401073796148842119413 2423006350668388953948695)
                      ·
                        rfl

theorem cell23_4718788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4718788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718788 prefixEnd_4718788 := by exact prefixLift 4718788
  have htrace : WordTrace (prefixWord ++ tailWord_4718788) baseStart_4718788 baseEnd_4718788 := by
    simpa [prefixWord, tailWord_4718788, baseEnd_4718788] using wordTrace_append hprefix tailTrace_4718788
  have hstable : (prefixWord ++ tailWord_4718788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718788).length < 2 ^ (prefixWord ++ tailWord_4718788).sum := by decide
  have hdescent : baseEnd_4718788 < baseStart_4718788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718805 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4718805 : Nat := 118140960795 + 4718805 * 2 ^ 59
def prefixEnd_4718805 : Nat := 4983230072969 + 3 ^ 40 * 4718805 * 2
def baseEnd_4718805 : Nat := 2423015079839515387436117

theorem tailTrace_4718805 : CollatzResearch.WordTrace tailWord_4718805 prefixEnd_4718805 2423015079839515387436117 := by
  unfold tailWord_4718805
  simp only [CollatzResearch.WordTrace]
  refine ⟨172108957669582867577517869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114739305113055245051678579 172108957669582867577517869)
  ·
    refine ⟨64540859126093575341569201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172108957669582867577517869 64540859126093575341569201)
    ·
      refine ⟨48405644344570181506176901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64540859126093575341569201 48405644344570181506176901)
      ·
        refine ⟨9076058314606909032408169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48405644344570181506176901 9076058314606909032408169)
        ·
          refine ⟨6807043735955181774306127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9076058314606909032408169 6807043735955181774306127)
          ·
            refine ⟨10210565603932772661459191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6807043735955181774306127 10210565603932772661459191)
            ·
              refine ⟨15315848405899158992188787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10210565603932772661459191 15315848405899158992188787)
              ·
                refine ⟨22973772608848738488283181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15315848405899158992188787 22973772608848738488283181)
                ·
                  refine ⟨8615164728318276933106193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22973772608848738488283181 8615164728318276933106193)
                  ·
                    refine ⟨6461373546238707699829645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8615164728318276933106193 6461373546238707699829645)
                    ·
                      refine ⟨2423015079839515387436117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461373546238707699829645 2423015079839515387436117)
                      ·
                        rfl

theorem cell23_4718805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4718805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718805 prefixEnd_4718805 := by exact prefixLift 4718805
  have htrace : WordTrace (prefixWord ++ tailWord_4718805) baseStart_4718805 baseEnd_4718805 := by
    simpa [prefixWord, tailWord_4718805, baseEnd_4718805] using wordTrace_append hprefix tailTrace_4718805
  have hstable : (prefixWord ++ tailWord_4718805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718805).length < 2 ^ (prefixWord ++ tailWord_4718805).sum := by decide
  have hdescent : baseEnd_4718805 < baseStart_4718805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718835 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 3]
def baseStart_4718835 : Nat := 118140960795 + 4718835 * 2 ^ 59
def prefixEnd_4718835 : Nat := 4983230072969 + 3 ^ 40 * 4718835 * 2
def baseEnd_4718835 : Nat := 2423030484259150270060979

theorem tailTrace_4718835 : CollatzResearch.WordTrace tailWord_4718835 prefixEnd_4718835 2423030484259150270060979 := by
  unfold tailWord_4718835
  simp only [CollatzResearch.WordTrace]
  refine ⟨172110051859474182701109959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114740034572982788467406639 172110051859474182701109959)
  ·
    refine ⟨258165077789211274051664939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172110051859474182701109959 258165077789211274051664939)
    ·
      refine ⟨387247616683816911077497409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258165077789211274051664939 387247616683816911077497409)
      ·
        refine ⟨290435712512862683308123057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387247616683816911077497409 290435712512862683308123057)
        ·
          refine ⟨217826784384647012481092293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290435712512862683308123057 217826784384647012481092293)
          ·
            refine ⟨40842522072121314840204805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217826784384647012481092293 40842522072121314840204805)
            ·
              refine ⟨7657972888522746532538401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40842522072121314840204805 7657972888522746532538401)
              ·
                refine ⟨5743479666392059899403801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7657972888522746532538401 5743479666392059899403801)
                ·
                  refine ⟨4307609749794044924552851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5743479666392059899403801 4307609749794044924552851)
                  ·
                    refine ⟨6461414624691067386829277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4307609749794044924552851 6461414624691067386829277)
                    ·
                      refine ⟨2423030484259150270060979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461414624691067386829277 2423030484259150270060979)
                      ·
                        rfl

theorem cell23_4718835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 3].length) (baseStart_4718835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718835 prefixEnd_4718835 := by exact prefixLift 4718835
  have htrace : WordTrace (prefixWord ++ tailWord_4718835) baseStart_4718835 baseEnd_4718835 := by
    simpa [prefixWord, tailWord_4718835, baseEnd_4718835] using wordTrace_append hprefix tailTrace_4718835
  have hstable : (prefixWord ++ tailWord_4718835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718835).length < 2 ^ (prefixWord ++ tailWord_4718835).sum := by decide
  have hdescent : baseEnd_4718835 < baseStart_4718835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718851 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 2, 6]
def baseStart_4718851 : Nat := 118140960795 + 4718851 * 2 ^ 59
def prefixEnd_4718851 : Nat := 4983230072969 + 3 ^ 40 * 4718851 * 2
def baseEnd_4718851 : Nat := 807679566649874069153635

theorem tailTrace_4718851 : CollatzResearch.WordTrace tailWord_4718851 prefixEnd_4718851 807679566649874069153635 := by
  unfold tailWord_4718851
  simp only [CollatzResearch.WordTrace]
  refine ⟨172110635427416217433692407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114740423618277478289128271 172110635427416217433692407)
  ·
    refine ⟨258165953141124326150538611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172110635427416217433692407 258165953141124326150538611)
    ·
      refine ⟨387248929711686489225807917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258165953141124326150538611 387248929711686489225807917)
      ·
        refine ⟨145218348641882433459677969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387248929711686489225807917 145218348641882433459677969)
        ·
          refine ⟨108913761481411825094758477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145218348641882433459677969 108913761481411825094758477)
          ·
            refine ⟨40842660555529434410534429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108913761481411825094758477 40842660555529434410534429)
            ·
              refine ⟨15315997708323537903950411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40842660555529434410534429 15315997708323537903950411)
              ·
                refine ⟨22973996562485306855925617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15315997708323537903950411 22973996562485306855925617)
                ·
                  refine ⟨17230497421863980141944213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22973996562485306855925617 17230497421863980141944213)
                  ·
                    refine ⟨807679566649874069153635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17230497421863980141944213 807679566649874069153635)
                    ·
                      rfl

theorem cell23_4718851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 6].length) (baseStart_4718851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718851 prefixEnd_4718851 := by exact prefixLift 4718851
  have htrace : WordTrace (prefixWord ++ tailWord_4718851) baseStart_4718851 baseEnd_4718851 := by
    simpa [prefixWord, tailWord_4718851, baseEnd_4718851] using wordTrace_append hprefix tailTrace_4718851
  have hstable : (prefixWord ++ tailWord_4718851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718851).length < 2 ^ (prefixWord ++ tailWord_4718851).sum := by decide
  have hdescent : baseEnd_4718851 < baseStart_4718851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718879 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 1, 3, 2]
def baseStart_4718879 : Nat := 118140960795 + 4718879 * 2 ^ 59
def prefixEnd_4718879 : Nat := 4983230072969 + 3 ^ 40 * 4718879 * 2
def baseEnd_4718879 : Nat := 2423053077407948097910777

theorem tailTrace_4718879 : CollatzResearch.WordTrace tailWord_4718879 prefixEnd_4718879 2423053077407948097910777 := by
  unfold tailWord_4718879
  simp only [CollatzResearch.WordTrace]
  refine ⟨172111656671314778215711691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114741104447543185477141127 172111656671314778215711691)
  ·
    refine ⟨258167485006972167323567537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172111656671314778215711691 258167485006972167323567537)
    ·
      refine ⟨193625613755229125492675653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258167485006972167323567537 193625613755229125492675653)
      ·
        refine ⟨36304802579105461029876685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193625613755229125492675653 36304802579105461029876685)
        ·
          refine ⟨13614300967164547886203757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36304802579105461029876685 13614300967164547886203757)
          ·
            refine ⟨5105362862686705457326409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13614300967164547886203757 5105362862686705457326409)
            ·
              refine ⟨3829022147015029092994807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5105362862686705457326409 3829022147015029092994807)
              ·
                refine ⟨5743533220522543639492211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829022147015029092994807 5743533220522543639492211)
                ·
                  refine ⟨8615299830783815459238317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743533220522543639492211 8615299830783815459238317)
                  ·
                    refine ⟨3230737436543930797214369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8615299830783815459238317 3230737436543930797214369)
                    ·
                      refine ⟨2423053077407948097910777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230737436543930797214369 2423053077407948097910777)
                      ·
                        rfl

theorem cell23_4718879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_4718879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718879 prefixEnd_4718879 := by exact prefixLift 4718879
  have htrace : WordTrace (prefixWord ++ tailWord_4718879) baseStart_4718879 baseEnd_4718879 := by
    simpa [prefixWord, tailWord_4718879, baseEnd_4718879] using wordTrace_append hprefix tailTrace_4718879
  have hstable : (prefixWord ++ tailWord_4718879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718879).length < 2 ^ (prefixWord ++ tailWord_4718879).sum := by decide
  have hdescent : baseEnd_4718879 < baseStart_4718879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718892 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 2, 2, 2]
def baseStart_4718892 : Nat := 118140960795 + 4718892 * 2 ^ 59
def prefixEnd_4718892 : Nat := 4983230072969 + 3 ^ 40 * 4718892 * 2
def baseEnd_4718892 : Nat := 2423059752656456547048217

theorem tailTrace_4718892 : CollatzResearch.WordTrace tailWord_4718892 prefixEnd_4718892 2423059752656456547048217 := by
  unfold tailWord_4718892
  simp only [CollatzResearch.WordTrace]
  refine ⟨86056065410133840717967465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114741420546845120957289953 86056065410133840717967465)
  ·
    refine ⟨64542049057600380538475599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86056065410133840717967465 64542049057600380538475599)
    ·
      refine ⟨96813073586400570807713399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64542049057600380538475599 96813073586400570807713399)
      ·
        refine ⟨145219610379600856211570099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96813073586400570807713399 145219610379600856211570099)
        ·
          refine ⟨217829415569401284317355149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145219610379600856211570099 217829415569401284317355149)
          ·
            refine ⟨81686030838525481619008181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217829415569401284317355149 81686030838525481619008181)
            ·
              refine ⟨7658065391111763901782017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81686030838525481619008181 7658065391111763901782017)
              ·
                refine ⟨5743549043333822926336513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7658065391111763901782017 5743549043333822926336513)
                ·
                  refine ⟨4307661782500367194752385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5743549043333822926336513 4307661782500367194752385)
                  ·
                    refine ⟨3230746336875275396064289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4307661782500367194752385 3230746336875275396064289)
                    ·
                      refine ⟨2423059752656456547048217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230746336875275396064289 2423059752656456547048217)
                      ·
                        rfl

theorem cell23_4718892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_4718892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718892 prefixEnd_4718892 := by exact prefixLift 4718892
  have htrace : WordTrace (prefixWord ++ tailWord_4718892) baseStart_4718892 baseEnd_4718892 := by
    simpa [prefixWord, tailWord_4718892, baseEnd_4718892] using wordTrace_append hprefix tailTrace_4718892
  have hstable : (prefixWord ++ tailWord_4718892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718892).length < 2 ^ (prefixWord ++ tailWord_4718892).sum := by decide
  have hdescent : baseEnd_4718892 < baseStart_4718892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718908 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_4718908 : Nat := 118140960795 + 4718908 * 2 ^ 59
def prefixEnd_4718908 : Nat := 4983230072969 + 3 ^ 40 * 4718908 * 2
def baseEnd_4718908 : Nat := 2423067968346928484448143

theorem tailTrace_4718908 : CollatzResearch.WordTrace tailWord_4718908 prefixEnd_4718908 2423067968346928484448143 := by
  unfold tailWord_4718908
  simp only [CollatzResearch.WordTrace]
  refine ⟨86056357194104858084258689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114741809592139810779011585 86056357194104858084258689)
  ·
    refine ⟨64542267895578643563194017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86056357194104858084258689 64542267895578643563194017)
    ·
      refine ⟨48406700921683982672395513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64542267895578643563194017 48406700921683982672395513)
      ·
        refine ⟨36305025691262987004296635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48406700921683982672395513 36305025691262987004296635)
        ·
          refine ⟨54457538536894480506444953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36305025691262987004296635 54457538536894480506444953)
          ·
            refine ⟨40843153902670860379833715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54457538536894480506444953 40843153902670860379833715)
            ·
              refine ⟨61264730854006290569750573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40843153902670860379833715 61264730854006290569750573)
              ·
                refine ⟨22974274070252358963656465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61264730854006290569750573 22974274070252358963656465)
                ·
                  refine ⟨17230705552689269222742349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22974274070252358963656465 17230705552689269222742349)
                  ·
                    refine ⟨6461514582258475958528381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17230705552689269222742349 6461514582258475958528381)
                    ·
                      refine ⟨2423067968346928484448143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461514582258475958528381 2423067968346928484448143)
                      ·
                        rfl

theorem cell23_4718908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_4718908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718908 prefixEnd_4718908 := by exact prefixLift 4718908
  have htrace : WordTrace (prefixWord ++ tailWord_4718908) baseStart_4718908 baseEnd_4718908 := by
    simpa [prefixWord, tailWord_4718908, baseEnd_4718908] using wordTrace_append hprefix tailTrace_4718908
  have hstable : (prefixWord ++ tailWord_4718908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718908).length < 2 ^ (prefixWord ++ tailWord_4718908).sum := by decide
  have hdescent : baseEnd_4718908 < baseStart_4718908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718911 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 3, 7]
def baseStart_4718911 : Nat := 118140960795 + 4718911 * 2 ^ 59
def prefixEnd_4718911 : Nat := 4983230072969 + 3 ^ 40 * 4718911 * 2
def baseEnd_4718911 : Nat := 807689836262963990903543

theorem tailTrace_4718911 : CollatzResearch.WordTrace tailWord_4718911 prefixEnd_4718911 807689836262963990903543 := by
  unfold tailWord_4718911
  simp only [CollatzResearch.WordTrace]
  refine ⟨172112823807198847680876587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114741882538132565120584391 172112823807198847680876587)
  ·
    refine ⟨258169235710798271521314881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172112823807198847680876587 258169235710798271521314881)
    ·
      refine ⟨193626926783098703640986161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258169235710798271521314881 193626926783098703640986161)
      ·
        refine ⟨145220195087324027730739621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193626926783098703640986161 145220195087324027730739621)
        ·
          refine ⟨27228786578873255199513679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145220195087324027730739621 27228786578873255199513679)
          ·
            refine ⟨40843179868309882799270519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27228786578873255199513679 40843179868309882799270519)
            ·
              refine ⟨61264769802464824198905779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40843179868309882799270519 61264769802464824198905779)
              ·
                refine ⟨91897154703697236298358669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61264769802464824198905779 91897154703697236298358669)
                ·
                  refine ⟨34461433013886463611884501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91897154703697236298358669 34461433013886463611884501)
                  ·
                    refine ⟨807689836262963990903543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34461433013886463611884501 807689836262963990903543)
                    ·
                      rfl

theorem cell23_4718911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_4718911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718911 prefixEnd_4718911 := by exact prefixLift 4718911
  have htrace : WordTrace (prefixWord ++ tailWord_4718911) baseStart_4718911 baseEnd_4718911 := by
    simpa [prefixWord, tailWord_4718911, baseEnd_4718911] using wordTrace_append hprefix tailTrace_4718911
  have hstable : (prefixWord ++ tailWord_4718911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718911).length < 2 ^ (prefixWord ++ tailWord_4718911).sum := by decide
  have hdescent : baseEnd_4718911 < baseStart_4718911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718921 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_4718921 : Nat := 118140960795 + 4718921 * 2 ^ 59
def prefixEnd_4718921 : Nat := 4983230072969 + 3 ^ 40 * 4718921 * 2
def baseEnd_4718921 : Nat := 2423074643595436933585583

theorem tailTrace_4718921 : CollatzResearch.WordTrace tailWord_4718921 prefixEnd_4718921 2423074643595436933585583 := by
  unfold tailWord_4718921
  simp only [CollatzResearch.WordTrace]
  refine ⟨172113188537162619388740617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114742125691441746259160411 172113188537162619388740617)
  ·
    refine ⟨129084891402871964541555463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172113188537162619388740617 129084891402871964541555463)
    ·
      refine ⟨193627337104307946812333195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129084891402871964541555463 193627337104307946812333195)
      ·
        refine ⟨290441005656461920218499793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193627337104307946812333195 290441005656461920218499793)
        ·
          refine ⟨217830754242346440163874845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290441005656461920218499793 217830754242346440163874845)
          ·
            refine ⟨81686532840879915061453067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217830754242346440163874845 81686532840879915061453067)
            ·
              refine ⟨122529799261319872592179601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81686532840879915061453067 122529799261319872592179601)
              ·
                refine ⟨91897349445989904444134701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122529799261319872592179601 91897349445989904444134701)
                ·
                  refine ⟨34461506042246214166550513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91897349445989904444134701 34461506042246214166550513)
                  ·
                    refine ⟨25846129531684660624912885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34461506042246214166550513 25846129531684660624912885)
                    ·
                      refine ⟨2423074643595436933585583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25846129531684660624912885 2423074643595436933585583)
                      ·
                        rfl

theorem cell23_4718921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_4718921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718921 prefixEnd_4718921 := by exact prefixLift 4718921
  have htrace : WordTrace (prefixWord ++ tailWord_4718921) baseStart_4718921 baseEnd_4718921 := by
    simpa [prefixWord, tailWord_4718921, baseEnd_4718921] using wordTrace_append hprefix tailTrace_4718921
  have hstable : (prefixWord ++ tailWord_4718921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718921).length < 2 ^ (prefixWord ++ tailWord_4718921).sum := by decide
  have hdescent : baseEnd_4718921 < baseStart_4718921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718932 : List Nat := [2, 4, 1, 1, 2, 4, 1, 3, 5]
def baseStart_4718932 : Nat := 118140960795 + 4718932 * 2 ^ 59
def prefixEnd_4718932 : Nat := 4983230072969 + 3 ^ 40 * 4718932 * 2
def baseEnd_4718932 : Nat := 269231143542515154505337

theorem tailTrace_4718932 : CollatzResearch.WordTrace tailWord_4718932 prefixEnd_4718932 269231143542515154505337 := by
  unfold tailWord_4718932
  simp only [CollatzResearch.WordTrace]
  refine ⟨86056794870061384133695525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114742393160081845511594033 86056794870061384133695525)
  ·
    refine ⟨16135649038136509525067911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86056794870061384133695525 16135649038136509525067911)
    ·
      refine ⟨24203473557204764287601867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16135649038136509525067911 24203473557204764287601867)
      ·
        refine ⟨36305210335807146431402801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24203473557204764287601867 36305210335807146431402801)
        ·
          refine ⟨27228907751855359823552101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36305210335807146431402801 27228907751855359823552101)
          ·
            refine ⟨5105420203472879966916019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27228907751855359823552101 5105420203472879966916019)
            ·
              refine ⟨7658130305209319950374029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5105420203472879966916019 7658130305209319950374029)
              ·
                refine ⟨2871798864453494981390261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7658130305209319950374029 2871798864453494981390261)
                ·
                  refine ⟨269231143542515154505337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2871798864453494981390261 269231143542515154505337)
                  ·
                    rfl

theorem cell23_4718932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_4718932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718932 prefixEnd_4718932 := by exact prefixLift 4718932
  have htrace : WordTrace (prefixWord ++ tailWord_4718932) baseStart_4718932 baseEnd_4718932 := by
    simpa [prefixWord, tailWord_4718932, baseEnd_4718932] using wordTrace_append hprefix tailTrace_4718932
  have hstable : (prefixWord ++ tailWord_4718932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718932).length < 2 ^ (prefixWord ++ tailWord_4718932).sum := by decide
  have hdescent : baseEnd_4718932 < baseStart_4718932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4718985 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 3]
def baseStart_4718985 : Nat := 118140960795 + 4718985 * 2 ^ 59
def prefixEnd_4718985 : Nat := 4983230072969 + 3 ^ 40 * 4718985 * 2
def baseEnd_4718985 : Nat := 2423107506357324683185289

theorem tailTrace_4718985 : CollatzResearch.WordTrace tailWord_4718985 prefixEnd_4718985 2423107506357324683185289 := by
  unfold tailWord_4718985
  simp only [CollatzResearch.WordTrace]
  refine ⟨172115522808930758319070409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114743681872620505546046939 172115522808930758319070409)
  ·
    refine ⟨129086642106698068739302807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172115522808930758319070409 129086642106698068739302807)
    ·
      refine ⟨193629963160047103108954211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129086642106698068739302807 193629963160047103108954211)
      ·
        refine ⟨290444944740070654663431317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193629963160047103108954211 290444944740070654663431317)
        ·
          refine ⟨13614606784690811937348343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 290444944740070654663431317 13614606784690811937348343)
          ·
            refine ⟨20421910177036217906022515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13614606784690811937348343 20421910177036217906022515)
            ·
              refine ⟨30632865265554326859033773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20421910177036217906022515 30632865265554326859033773)
              ·
                refine ⟨11487324474582872572137665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30632865265554326859033773 11487324474582872572137665)
                ·
                  refine ⟨8615493355937154429103249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11487324474582872572137665 8615493355937154429103249)
                  ·
                    refine ⟨6461620016952865821827437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8615493355937154429103249 6461620016952865821827437)
                    ·
                      refine ⟨2423107506357324683185289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461620016952865821827437 2423107506357324683185289)
                      ·
                        rfl

theorem cell23_4718985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_4718985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4718985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4718985 prefixEnd_4718985 := by exact prefixLift 4718985
  have htrace : WordTrace (prefixWord ++ tailWord_4718985) baseStart_4718985 baseEnd_4718985 := by
    simpa [prefixWord, tailWord_4718985, baseEnd_4718985] using wordTrace_append hprefix tailTrace_4718985
  have hstable : (prefixWord ++ tailWord_4718985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4718985).length < 2 ^ (prefixWord ++ tailWord_4718985).sum := by decide
  have hdescent : baseEnd_4718985 < baseStart_4718985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4718985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719052 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_4719052 : Nat := 118140960795 + 4719052 * 2 ^ 59
def prefixEnd_4719052 : Nat := 4983230072969 + 3 ^ 40 * 4719052 * 2
def baseEnd_4719052 : Nat := 807713969853725307015827

theorem tailTrace_4719052 : CollatzResearch.WordTrace tailWord_4719052 prefixEnd_4719052 807713969853725307015827 := by
  unfold tailWord_4719052
  simp only [CollatzResearch.WordTrace]
  refine ⟨86058983249844014380879705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114745310999792019174506273 86058983249844014380879705)
  ·
    refine ⟨64544237437383010785659779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86058983249844014380879705 64544237437383010785659779)
    ·
      refine ⟨96816356156074516178489669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64544237437383010785659779 96816356156074516178489669)
      ·
        refine ⟨18153066779263971783466813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96816356156074516178489669 18153066779263971783466813)
        ·
          refine ⟨6807400042223989418800055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18153066779263971783466813 6807400042223989418800055)
          ·
            refine ⟨10211100063335984128200083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6807400042223989418800055 10211100063335984128200083)
            ·
              refine ⟨15316650095003976192300125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10211100063335984128200083 15316650095003976192300125)
              ·
                refine ⟨5743743785626491072112547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15316650095003976192300125 5743743785626491072112547)
                ·
                  refine ⟨8615615678439736608168821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743743785626491072112547 8615615678439736608168821)
                  ·
                    refine ⟨807713969853725307015827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8615615678439736608168821 807713969853725307015827)
                    ·
                      rfl

theorem cell23_4719052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_4719052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719052 prefixEnd_4719052 := by exact prefixLift 4719052
  have htrace : WordTrace (prefixWord ++ tailWord_4719052) baseStart_4719052 baseEnd_4719052 := by
    simpa [prefixWord, tailWord_4719052, baseEnd_4719052] using wordTrace_append hprefix tailTrace_4719052
  have hstable : (prefixWord ++ tailWord_4719052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719052).length < 2 ^ (prefixWord ++ tailWord_4719052).sum := by decide
  have hdescent : baseEnd_4719052 < baseStart_4719052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719065 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 4, 4]
def baseStart_4719065 : Nat := 118140960795 + 4719065 * 2 ^ 59
def prefixEnd_4719065 : Nat := 4983230072969 + 3 ^ 40 * 4719065 * 2
def baseEnd_4719065 : Nat := 807716194936561456728307

theorem tailTrace_4719065 : CollatzResearch.WordTrace tailWord_4719065 prefixEnd_4719065 807716194936561456728307 := by
  unfold tailWord_4719065
  simp only [CollatzResearch.WordTrace]
  refine ⟨172118440648640931981982649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114745627099093954654655099 172118440648640931981982649)
  ·
    refine ⟨129088830486480698986486987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172118440648640931981982649 129088830486480698986486987)
    ·
      refine ⟨193633245729721048479730481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129088830486480698986486987 193633245729721048479730481)
      ·
        refine ⟨145224934297290786359797861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193633245729721048479730481 145224934297290786359797861)
        ·
          refine ⟨27229675180742022442462099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145224934297290786359797861 27229675180742022442462099)
          ·
            refine ⟨40844512771113033663693149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27229675180742022442462099 40844512771113033663693149)
            ·
              refine ⟨15316692289167387623884931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40844512771113033663693149 15316692289167387623884931)
              ·
                refine ⟨22975038433751081435827397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15316692289167387623884931 22975038433751081435827397)
                ·
                  refine ⟨4307819706328327769217637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22975038433751081435827397 4307819706328327769217637)
                  ·
                    refine ⟨807716194936561456728307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307819706328327769217637 807716194936561456728307)
                    ·
                      rfl

theorem cell23_4719065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_4719065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719065 prefixEnd_4719065 := by exact prefixLift 4719065
  have htrace : WordTrace (prefixWord ++ tailWord_4719065) baseStart_4719065 baseEnd_4719065 := by
    simpa [prefixWord, tailWord_4719065, baseEnd_4719065] using wordTrace_append hprefix tailTrace_4719065
  have hstable : (prefixWord ++ tailWord_4719065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719065).length < 2 ^ (prefixWord ++ tailWord_4719065).sum := by decide
  have hdescent : baseEnd_4719065 < baseStart_4719065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
