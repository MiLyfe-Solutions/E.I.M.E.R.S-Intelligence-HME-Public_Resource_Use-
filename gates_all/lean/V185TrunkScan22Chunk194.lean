import V185TrunkScan22Chunk193

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1728007 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1728007 : Nat := 118140960795 + 1728007 * 2 ^ 59
def prefixEnd_1728007 : Nat := 4983230072969 + 3 ^ 40 * 1728007 * 2
def baseEnd_1728007 : Nat := 591532110222617265577031

theorem tailTrace_1728007 : CollatzResearch.WordTrace tailWord_1728007 prefixEnd_1728007 591532110222617265577031 := by
  unfold tailWord_1728007
  simp only [CollatzResearch.WordTrace]
  refine ⟨63025593050733233944998275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42017062033822155963332183 63025593050733233944998275)
  ·
    refine ⟨94538389576099850917497413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63025593050733233944998275 94538389576099850917497413)
    ·
      refine ⟨17725948045518722047030765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94538389576099850917497413 17725948045518722047030765)
      ·
        refine ⟨6647230517069520767636537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17725948045518722047030765 6647230517069520767636537)
        ·
          refine ⟨4985422887802140575727403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6647230517069520767636537 4985422887802140575727403)
          ·
            refine ⟨7478134331703210863591105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985422887802140575727403 7478134331703210863591105)
            ·
              refine ⟨5608600748777408147693329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7478134331703210863591105 5608600748777408147693329)
              ·
                refine ⟨4206450561583056110769997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608600748777408147693329 4206450561583056110769997)
                ·
                  refine ⟨1577418960593646041538749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4206450561583056110769997 1577418960593646041538749)
                  ·
                    refine ⟨591532110222617265577031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577418960593646041538749 591532110222617265577031)
                    ·
                      rfl

theorem cell22_1728007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1728007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728007 prefixEnd_1728007 := by exact prefixLift 1728007
  have htrace : WordTrace (prefixWord ++ tailWord_1728007) baseStart_1728007 baseEnd_1728007 := by
    simpa [prefixWord, tailWord_1728007, baseEnd_1728007] using wordTrace_append hprefix tailTrace_1728007
  have hstable : (prefixWord ++ tailWord_1728007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728007).length < 2 ^ (prefixWord ++ tailWord_1728007).sum := by decide
  have hdescent : baseEnd_1728007 < baseStart_1728007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728050 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1728050 : Nat := 118140960795 + 1728050 * 2 ^ 59
def prefixEnd_1728050 : Nat := 4983230072969 + 3 ^ 40 * 1728050 * 2
def baseEnd_1728050 : Nat := 591546830001379486751899

theorem tailTrace_1728050 : CollatzResearch.WordTrace tailWord_1728050 prefixEnd_1728050 591546830001379486751899 := by
  unfold tailWord_1728050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15756790347394363072203401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42018107593051634859209069 15756790347394363072203401)
  ·
    refine ⟨11817592760545772304152551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15756790347394363072203401 11817592760545772304152551)
    ·
      refine ⟨17726389140818658456228827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11817592760545772304152551 17726389140818658456228827)
      ·
        refine ⟨26589583711227987684343241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17726389140818658456228827 26589583711227987684343241)
        ·
          refine ⟨19942187783420990763257431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26589583711227987684343241 19942187783420990763257431)
          ·
            refine ⟨29913281675131486144886147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19942187783420990763257431 29913281675131486144886147)
            ·
              refine ⟨44869922512697229217329221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29913281675131486144886147 44869922512697229217329221)
              ·
                refine ⟨8413110471130730478249229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44869922512697229217329221 8413110471130730478249229)
                ·
                  refine ⟨3154916426674023929343461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8413110471130730478249229 3154916426674023929343461)
                  ·
                    refine ⟨591546830001379486751899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3154916426674023929343461 591546830001379486751899)
                    ·
                      rfl

theorem cell22_1728050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1728050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728050 prefixEnd_1728050 := by exact prefixLift 1728050
  have htrace : WordTrace (prefixWord ++ tailWord_1728050) baseStart_1728050 baseEnd_1728050 := by
    simpa [prefixWord, tailWord_1728050, baseEnd_1728050] using wordTrace_append hprefix tailTrace_1728050
  have hstable : (prefixWord ++ tailWord_1728050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728050).length < 2 ^ (prefixWord ++ tailWord_1728050).sum := by decide
  have hdescent : baseEnd_1728050 < baseStart_1728050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728054 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_1728054 : Nat := 118140960795 + 1728054 * 2 ^ 59
def prefixEnd_1728054 : Nat := 4983230072969 + 3 ^ 40 * 1728054 * 2
def baseEnd_1728054 : Nat := 197182733094374936550629

theorem tailTrace_1728054 : CollatzResearch.WordTrace tailWord_1728054 prefixEnd_1728054 197182733094374936550629 := by
  unfold tailWord_1728054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3939206705097685060747451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42018204854375307314639477 3939206705097685060747451)
  ·
    refine ⟨5908810057646527591121177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3939206705097685060747451 5908810057646527591121177)
    ·
      refine ⟨4431607543234895693340883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5908810057646527591121177 4431607543234895693340883)
      ·
        refine ⟨6647411314852343540011325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431607543234895693340883 6647411314852343540011325)
        ·
          refine ⟨2492779243069628827504247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6647411314852343540011325 2492779243069628827504247)
          ·
            refine ⟨3739168864604443241256371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492779243069628827504247 3739168864604443241256371)
            ·
              refine ⟨5608753296906664861884557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739168864604443241256371 5608753296906664861884557)
              ·
                refine ⟨2103282486339999323206709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5608753296906664861884557 2103282486339999323206709)
                ·
                  refine ⟨197182733094374936550629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103282486339999323206709 197182733094374936550629)
                  ·
                    rfl

theorem cell22_1728054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_1728054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728054 prefixEnd_1728054 := by exact prefixLift 1728054
  have htrace : WordTrace (prefixWord ++ tailWord_1728054) baseStart_1728054 baseEnd_1728054 := by
    simpa [prefixWord, tailWord_1728054, baseEnd_1728054] using wordTrace_append hprefix tailTrace_1728054
  have hstable : (prefixWord ++ tailWord_1728054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728054).length < 2 ^ (prefixWord ++ tailWord_1728054).sum := by decide
  have hdescent : baseEnd_1728054 < baseStart_1728054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728065 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 8]
def baseStart_1728065 : Nat := 118140960795 + 1728065 * 2 ^ 59
def prefixEnd_1728065 : Nat := 4983230072969 + 3 ^ 40 * 1728065 * 2
def baseEnd_1728065 : Nat := 197183988269308149208951

theorem tailTrace_1728065 : CollatzResearch.WordTrace tailWord_1728065 prefixEnd_1728065 197183988269308149208951 := by
  unfold tailWord_1728065
  simp only [CollatzResearch.WordTrace]
  refine ⟨63027708484523109850609649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42018472323015406567073099 63027708484523109850609649)
  ·
    refine ⟨47270781363392332387957237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63027708484523109850609649 47270781363392332387957237)
    ·
      refine ⟨4431635752818031161370991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47270781363392332387957237 4431635752818031161370991)
      ·
        refine ⟨6647453629227046742056487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431635752818031161370991 6647453629227046742056487)
        ·
          refine ⟨9971180443840570113084731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647453629227046742056487 9971180443840570113084731)
          ·
            refine ⟨14956770665760855169627097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9971180443840570113084731 14956770665760855169627097)
            ·
              refine ⟨11217577999320641377220323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14956770665760855169627097 11217577999320641377220323)
              ·
                refine ⟨16826366998980962065830485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11217577999320641377220323 16826366998980962065830485)
                ·
                  refine ⟨197183988269308149208951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16826366998980962065830485 197183988269308149208951)
                  ·
                    rfl

theorem cell22_1728065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_1728065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728065 prefixEnd_1728065 := by exact prefixLift 1728065
  have htrace : WordTrace (prefixWord ++ tailWord_1728065) baseStart_1728065 baseEnd_1728065 := by
    simpa [prefixWord, tailWord_1728065, baseEnd_1728065] using wordTrace_append hprefix tailTrace_1728065
  have hstable : (prefixWord ++ tailWord_1728065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728065).length < 2 ^ (prefixWord ++ tailWord_1728065).sum := by decide
  have hdescent : baseEnd_1728065 < baseStart_1728065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728080 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_1728080 : Nat := 118140960795 + 1728080 * 2 ^ 59
def prefixEnd_1728080 : Nat := 4983230072969 + 3 ^ 40 * 1728080 * 2
def baseEnd_1728080 : Nat := 591557099614469408501807

theorem tailTrace_1728080 : CollatzResearch.WordTrace tailWord_1728080 prefixEnd_1728080 591557099614469408501807 := by
  unfold tailWord_1728080
  simp only [CollatzResearch.WordTrace]
  refine ⟨31514127789734383706202847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42018837052979178274937129 31514127789734383706202847)
  ·
    refine ⟨47271191684601575559304271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31514127789734383706202847 47271191684601575559304271)
    ·
      refine ⟨70906787526902363338956407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47271191684601575559304271 70906787526902363338956407)
      ·
        refine ⟨106360181290353545008434611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70906787526902363338956407 106360181290353545008434611)
        ·
          refine ⟨159540271935530317512651917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106360181290353545008434611 159540271935530317512651917)
          ·
            refine ⟨59827601975823869067244469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159540271935530317512651917 59827601975823869067244469)
            ·
              refine ⟨5608837685233487725054169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59827601975823869067244469 5608837685233487725054169)
              ·
                refine ⟨4206628263925115793790627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608837685233487725054169 4206628263925115793790627)
                ·
                  refine ⟨6309942395887673690685941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206628263925115793790627 6309942395887673690685941)
                  ·
                    refine ⟨591557099614469408501807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6309942395887673690685941 591557099614469408501807)
                    ·
                      rfl

theorem cell22_1728080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_1728080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728080 prefixEnd_1728080 := by exact prefixLift 1728080
  have htrace : WordTrace (prefixWord ++ tailWord_1728080) baseStart_1728080 baseEnd_1728080 := by
    simpa [prefixWord, tailWord_1728080, baseEnd_1728080] using wordTrace_append hprefix tailTrace_1728080
  have hstable : (prefixWord ++ tailWord_1728080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728080).length < 2 ^ (prefixWord ++ tailWord_1728080).sum := by decide
  have hdescent : baseEnd_1728080 < baseStart_1728080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728084 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_1728084 : Nat := 118140960795 + 1728084 * 2 ^ 59
def prefixEnd_1728084 : Nat := 4983230072969 + 3 ^ 40 * 1728084 * 2
def baseEnd_1728084 : Nat := 591558468896214731401795

theorem tailTrace_1728084 : CollatzResearch.WordTrace tailWord_1728084 prefixEnd_1728084 591558468896214731401795 := by
  unfold tailWord_1728084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31514200735727138047775653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42018934314302850730367537 31514200735727138047775653)
  ·
    refine ⟨5908912637948838383957935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31514200735727138047775653 5908912637948838383957935)
    ·
      refine ⟨8863368956923257575936903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908912637948838383957935 8863368956923257575936903)
      ·
        refine ⟨13295053435384886363905355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863368956923257575936903 13295053435384886363905355)
        ·
          refine ⟨19942580153077329545858033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295053435384886363905355 19942580153077329545858033)
          ·
            refine ⟨14956935114807997159393525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19942580153077329545858033 14956935114807997159393525)
            ·
              refine ⟨1402212667013249733693143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14956935114807997159393525 1402212667013249733693143)
              ·
                refine ⟨2103319000519874600539715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402212667013249733693143 2103319000519874600539715)
                ·
                  refine ⟨3154978500779811900809573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103319000519874600539715 3154978500779811900809573)
                  ·
                    refine ⟨591558468896214731401795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3154978500779811900809573 591558468896214731401795)
                    ·
                      rfl

theorem cell22_1728084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_1728084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728084 prefixEnd_1728084 := by exact prefixLift 1728084
  have htrace : WordTrace (prefixWord ++ tailWord_1728084) baseStart_1728084 baseEnd_1728084 := by
    simpa [prefixWord, tailWord_1728084, baseEnd_1728084] using wordTrace_append hprefix tailTrace_1728084
  have hstable : (prefixWord ++ tailWord_1728084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728084).length < 2 ^ (prefixWord ++ tailWord_1728084).sum := by decide
  have hdescent : baseEnd_1728084 < baseStart_1728084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728099 : List Nat := [1, 1, 1, 5, 1, 3, 4, 2, 4]
def baseStart_1728099 : Nat := 118140960795 + 1728099 * 2 ^ 59
def prefixEnd_1728099 : Nat := 4983230072969 + 3 ^ 40 * 1728099 * 2
def baseEnd_1728099 : Nat := 197187867900919897425583

theorem tailTrace_1728099 : CollatzResearch.WordTrace tailWord_1728099 prefixEnd_1728099 197187867900919897425583 := by
  unfold tailWord_1728099
  simp only [CollatzResearch.WordTrace]
  refine ⟨63028948566399933657347351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42019299044266622438231567 63028948566399933657347351)
  ·
    refine ⟨94543422849599900486021027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63028948566399933657347351 94543422849599900486021027)
    ·
      refine ⟨141815134274399850729031541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94543422849599900486021027 141815134274399850729031541)
      ·
        refine ⟨13295168838224986005846707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141815134274399850729031541 13295168838224986005846707)
        ·
          refine ⟨19942753257337479008770061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295168838224986005846707 19942753257337479008770061)
          ·
            refine ⟨7478532471501554628288773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19942753257337479008770061 7478532471501554628288773)
            ·
              refine ⟨1402224838406541492804145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7478532471501554628288773 1402224838406541492804145)
              ·
                refine ⟨1051668628804906119603109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402224838406541492804145 1051668628804906119603109)
                ·
                  refine ⟨197187867900919897425583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051668628804906119603109 197187867900919897425583)
                  ·
                    rfl

theorem cell22_1728099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 4].length) (baseStart_1728099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728099 prefixEnd_1728099 := by exact prefixLift 1728099
  have htrace : WordTrace (prefixWord ++ tailWord_1728099) baseStart_1728099 baseEnd_1728099 := by
    simpa [prefixWord, tailWord_1728099, baseEnd_1728099] using wordTrace_append hprefix tailTrace_1728099
  have hstable : (prefixWord ++ tailWord_1728099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728099).length < 2 ^ (prefixWord ++ tailWord_1728099).sum := by decide
  have hdescent : baseEnd_1728099 < baseStart_1728099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728114 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_1728114 : Nat := 118140960795 + 1728114 * 2 ^ 59
def prefixEnd_1728114 : Nat := 4983230072969 + 3 ^ 40 * 1728114 * 2
def baseEnd_1728114 : Nat := 591568738509304653151703

theorem tailTrace_1728114 : CollatzResearch.WordTrace tailWord_1728114 prefixEnd_1728114 591568738509304653151703 := by
  unfold tailWord_1728114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757373915336397804785849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42019663774230394146095597 15757373915336397804785849)
  ·
    refine ⟨11818030436502298353589387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15757373915336397804785849 11818030436502298353589387)
    ·
      refine ⟨17727045654753447530384081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11818030436502298353589387 17727045654753447530384081)
      ·
        refine ⟨13295284241065085647788061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17727045654753447530384081 13295284241065085647788061)
        ·
          refine ⟨4985731590399407117920523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13295284241065085647788061 4985731590399407117920523)
          ·
            refine ⟨7478597385599110676880785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985731590399407117920523 7478597385599110676880785)
            ·
              refine ⟨5608948039199333007660589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7478597385599110676880785 5608948039199333007660589)
              ·
                refine ⟨2103355514699749877872721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5608948039199333007660589 2103355514699749877872721)
                ·
                  refine ⟨1577516636024812408404541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103355514699749877872721 1577516636024812408404541)
                  ·
                    refine ⟨591568738509304653151703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577516636024812408404541 591568738509304653151703)
                    ·
                      rfl

theorem cell22_1728114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_1728114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728114 prefixEnd_1728114 := by exact prefixLift 1728114
  have htrace : WordTrace (prefixWord ++ tailWord_1728114) baseStart_1728114 baseEnd_1728114 := by
    simpa [prefixWord, tailWord_1728114, baseEnd_1728114] using wordTrace_append hprefix tailTrace_1728114
  have hstable : (prefixWord ++ tailWord_1728114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728114).length < 2 ^ (prefixWord ++ tailWord_1728114).sum := by decide
  have hdescent : baseEnd_1728114 < baseStart_1728114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728129 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1728129 : Nat := 118140960795 + 1728129 * 2 ^ 59
def prefixEnd_1728129 : Nat := 4983230072969 + 3 ^ 40 * 1728129 * 2
def baseEnd_1728129 : Nat := 591573873315849614026657

theorem tailTrace_1728129 : CollatzResearch.WordTrace tailWord_1728129 prefixEnd_1728129 591573873315849614026657 := by
  unfold tailWord_1728129
  simp only [CollatzResearch.WordTrace]
  refine ⟨63030042756291248780939441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42020028504194165853959627 63030042756291248780939441)
  ·
    refine ⟨47272532067218436585704581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63030042756291248780939441 47272532067218436585704581)
    ·
      refine ⟨8863599762603456859819609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47272532067218436585704581 8863599762603456859819609)
      ·
        refine ⟨6647699821952592644864707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8863599762603456859819609 6647699821952592644864707)
        ·
          refine ⟨9971549732928888967297061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647699821952592644864707 9971549732928888967297061)
          ·
            refine ⟨1869665574924166681368199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9971549732928888967297061 1869665574924166681368199)
            ·
              refine ⟨2804498362386250022052299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869665574924166681368199 2804498362386250022052299)
              ·
                refine ⟨4206747543579375033078449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804498362386250022052299 4206747543579375033078449)
                ·
                  refine ⟨3155060657684531274808837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4206747543579375033078449 3155060657684531274808837)
                  ·
                    refine ⟨591573873315849614026657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155060657684531274808837 591573873315849614026657)
                    ·
                      rfl

theorem cell22_1728129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1728129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728129 prefixEnd_1728129 := by exact prefixLift 1728129
  have htrace : WordTrace (prefixWord ++ tailWord_1728129) baseStart_1728129 baseEnd_1728129 := by
    simpa [prefixWord, tailWord_1728129, baseEnd_1728129] using wordTrace_append hprefix tailTrace_1728129
  have hstable : (prefixWord ++ tailWord_1728129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728129).length < 2 ^ (prefixWord ++ tailWord_1728129).sum := by decide
  have hdescent : baseEnd_1728129 < baseStart_1728129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728148 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1728148 : Nat := 118140960795 + 1728148 * 2 ^ 59
def prefixEnd_1728148 : Nat := 4983230072969 + 3 ^ 40 * 1728148 * 2
def baseEnd_1728148 : Nat := 591580377404139897801599

theorem tailTrace_1728148 : CollatzResearch.WordTrace tailWord_1728148 prefixEnd_1728148 591580377404139897801599 := by
  unfold tailWord_1728148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31515367871611207512940549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42020490495481610017254065 31515367871611207512940549)
  ·
    refine ⟨5909131475927101408676353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31515367871611207512940549 5909131475927101408676353)
    ·
      refine ⟨4431848606945326056507265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5909131475927101408676353 4431848606945326056507265)
      ·
        refine ⟨3323886455208994542380449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4431848606945326056507265 3323886455208994542380449)
        ·
          refine ⟨2492914841406745906785337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3323886455208994542380449 2492914841406745906785337)
          ·
            refine ⟨1869686131055059430089003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2492914841406745906785337 1869686131055059430089003)
            ·
              refine ⟨2804529196582589145133505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869686131055059430089003 2804529196582589145133505)
              ·
                refine ⟨2103396897436941858850129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804529196582589145133505 2103396897436941858850129)
                ·
                  refine ⟨1577547673077706394137597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103396897436941858850129 1577547673077706394137597)
                  ·
                    refine ⟨591580377404139897801599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577547673077706394137597 591580377404139897801599)
                    ·
                      rfl

theorem cell22_1728148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1728148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728148 prefixEnd_1728148 := by exact prefixLift 1728148
  have htrace : WordTrace (prefixWord ++ tailWord_1728148) baseStart_1728148 baseEnd_1728148 := by
    simpa [prefixWord, tailWord_1728148, baseEnd_1728148] using wordTrace_append hprefix tailTrace_1728148
  have hstable : (prefixWord ++ tailWord_1728148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728148).length < 2 ^ (prefixWord ++ tailWord_1728148).sum := by decide
  have hdescent : baseEnd_1728148 < baseStart_1728148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728217 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 6]
def baseStart_1728217 : Nat := 118140960795 + 1728217 * 2 ^ 59
def prefixEnd_1728217 : Nat := 4983230072969 + 3 ^ 40 * 1728217 * 2
def baseEnd_1728217 : Nat := 197201332504748905942129

theorem tailTrace_1728217 : CollatzResearch.WordTrace tailWord_1728217 prefixEnd_1728217 197201332504748905942129 := by
  unfold tailWord_1728217
  simp only [CollatzResearch.WordTrace]
  refine ⟨63033252379972439810142905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42022168253314959873428603 63033252379972439810142905)
  ·
    refine ⟨47274939284979329857607179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63033252379972439810142905 47274939284979329857607179)
    ·
      refine ⟨70912408927468994786410769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47274939284979329857607179 70912408927468994786410769)
      ·
        refine ⟨53184306695601746089808077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70912408927468994786410769 53184306695601746089808077)
        ·
          refine ⟨19944115010850654783678029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53184306695601746089808077 19944115010850654783678029)
          ·
            refine ⟨7479043129068995543879261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19944115010850654783678029 7479043129068995543879261)
            ·
              refine ⟨2804641173400873328954723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7479043129068995543879261 2804641173400873328954723)
              ·
                refine ⟨4206961760101309993432085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804641173400873328954723 4206961760101309993432085)
                ·
                  refine ⟨197201332504748905942129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4206961760101309993432085 197201332504748905942129)
                  ·
                    rfl

theorem cell22_1728217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_1728217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728217 prefixEnd_1728217 := by exact prefixLift 1728217
  have htrace : WordTrace (prefixWord ++ tailWord_1728217) baseStart_1728217 baseEnd_1728217 := by
    simpa [prefixWord, tailWord_1728217, baseEnd_1728217] using wordTrace_append hprefix tailTrace_1728217
  have hstable : (prefixWord ++ tailWord_1728217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728217).length < 2 ^ (prefixWord ++ tailWord_1728217).sum := by decide
  have hdescent : baseEnd_1728217 < baseStart_1728217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728247 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1728247 : Nat := 118140960795 + 1728247 * 2 ^ 59
def prefixEnd_1728247 : Nat := 4983230072969 + 3 ^ 40 * 1728247 * 2
def baseEnd_1728247 : Nat := 591614267127336639576295

theorem tailTrace_1728247 : CollatzResearch.WordTrace tailWord_1728247 prefixEnd_1728247 591614267127336639576295 := by
  unfold tailWord_1728247
  simp only [CollatzResearch.WordTrace]
  refine ⟨63034346569863754933734995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42022897713242503289156663 63034346569863754933734995)
  ·
    refine ⟨94551519854795632400602493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63034346569863754933734995 94551519854795632400602493)
    ·
      refine ⟨35456819945548362150225935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94551519854795632400602493 35456819945548362150225935)
      ·
        refine ⟨53185229918322543225338903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35456819945548362150225935 53185229918322543225338903)
        ·
          refine ⟨79777844877483814838008355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53185229918322543225338903 79777844877483814838008355)
          ·
            refine ⟨119666767316225722257012533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79777844877483814838008355 119666767316225722257012533)
            ·
              refine ⟨11218759435896161461594925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119666767316225722257012533 11218759435896161461594925)
              ·
                refine ⟨4207034788461060548098097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11218759435896161461594925 4207034788461060548098097)
                ·
                  refine ⟨3155276091345795411073573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207034788461060548098097 3155276091345795411073573)
                  ·
                    refine ⟨591614267127336639576295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155276091345795411073573 591614267127336639576295)
                    ·
                      rfl

theorem cell22_1728247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1728247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728247 prefixEnd_1728247 := by exact prefixLift 1728247
  have htrace : WordTrace (prefixWord ++ tailWord_1728247) baseStart_1728247 baseEnd_1728247 := by
    simpa [prefixWord, tailWord_1728247, baseEnd_1728247] using wordTrace_append hprefix tailTrace_1728247
  have hstable : (prefixWord ++ tailWord_1728247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728247).length < 2 ^ (prefixWord ++ tailWord_1728247).sum := by decide
  have hdescent : baseEnd_1728247 < baseStart_1728247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728266 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_1728266 : Nat := 118140960795 + 1728266 * 2 ^ 59
def prefixEnd_1728266 : Nat := 4983230072969 + 3 ^ 40 * 1728266 * 2
def baseEnd_1728266 : Nat := 591620771215626923351237

theorem tailTrace_1728266 : CollatzResearch.WordTrace tailWord_1728266 prefixEnd_1728266 591620771215626923351237 := by
  unfold tailWord_1728266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758759889198730294669163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42023359704529947452451101 15758759889198730294669163)
  ·
    refine ⟨23638139833798095442003745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15758759889198730294669163 23638139833798095442003745)
    ·
      refine ⟨17728604875348571581502809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23638139833798095442003745 17728604875348571581502809)
      ·
        refine ⟨13296453656511428686127107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17728604875348571581502809 13296453656511428686127107)
        ·
          refine ⟨19944680484767143029190661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13296453656511428686127107 19944680484767143029190661)
          ·
            refine ⟨3739627590893839317973249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19944680484767143029190661 3739627590893839317973249)
            ·
              refine ⟨2804720693170379488479937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739627590893839317973249 2804720693170379488479937)
              ·
                refine ⟨2103540519877784616359953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804720693170379488479937 2103540519877784616359953)
                ·
                  refine ⟨1577655389908338462269965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103540519877784616359953 1577655389908338462269965)
                  ·
                    refine ⟨591620771215626923351237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577655389908338462269965 591620771215626923351237)
                    ·
                      rfl

theorem cell22_1728266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_1728266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728266 prefixEnd_1728266 := by exact prefixLift 1728266
  have htrace : WordTrace (prefixWord ++ tailWord_1728266) baseStart_1728266 baseEnd_1728266 := by
    simpa [prefixWord, tailWord_1728266, baseEnd_1728266] using wordTrace_append hprefix tailTrace_1728266
  have hstable : (prefixWord ++ tailWord_1728266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728266).length < 2 ^ (prefixWord ++ tailWord_1728266).sum := by decide
  have hdescent : baseEnd_1728266 < baseStart_1728266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728279 : List Nat := [1, 1, 3, 4, 2, 3, 1, 7]
def baseStart_1728279 : Nat := 118140960795 + 1728279 * 2 ^ 59
def prefixEnd_1728279 : Nat := 4983230072969 + 3 ^ 40 * 1728279 * 2
def baseEnd_1728279 : Nat := 65736135709033246975133

theorem tailTrace_1728279 : CollatzResearch.WordTrace tailWord_1728279 prefixEnd_1728279 65736135709033246975133 := by
  unfold tailWord_1728279
  simp only [CollatzResearch.WordTrace]
  refine ⟨63035513705747824398899891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42023675803831882932599927 63035513705747824398899891)
  ·
    refine ⟨94553270558621736598349837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63035513705747824398899891 94553270558621736598349837)
    ·
      refine ⟨35457476459483151224381189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94553270558621736598349837 35457476459483151224381189)
      ·
        refine ⟨6648276836153090854571473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35457476459483151224381189 6648276836153090854571473)
        ·
          refine ⟨4986207627114818140928605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6648276836153090854571473 4986207627114818140928605)
          ·
            refine ⟨1869827860168056802848227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4986207627114818140928605 1869827860168056802848227)
            ·
              refine ⟨2804741790252085204272341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869827860168056802848227 2804741790252085204272341)
              ·
                refine ⟨65736135709033246975133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2804741790252085204272341 65736135709033246975133)
                ·
                  rfl

theorem cell22_1728279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 7].length) (baseStart_1728279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728279 prefixEnd_1728279 := by exact prefixLift 1728279
  have htrace : WordTrace (prefixWord ++ tailWord_1728279) baseStart_1728279 baseEnd_1728279 := by
    simpa [prefixWord, tailWord_1728279, baseEnd_1728279] using wordTrace_append hprefix tailTrace_1728279
  have hstable : (prefixWord ++ tailWord_1728279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728279).length < 2 ^ (prefixWord ++ tailWord_1728279).sum := by decide
  have hdescent : baseEnd_1728279 < baseStart_1728279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728341 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 5]
def baseStart_1728341 : Nat := 118140960795 + 1728341 * 2 ^ 59
def prefixEnd_1728341 : Nat := 4983230072969 + 3 ^ 40 * 1728341 * 2
def baseEnd_1728341 : Nat := 197215481749450575908669

theorem tailTrace_1728341 : CollatzResearch.WordTrace tailWord_1728341 prefixEnd_1728341 197215481749450575908669 := by
  unfold tailWord_1728341
  simp only [CollatzResearch.WordTrace]
  refine ⟨63037775031523208987656877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42025183354348805991771251 63037775031523208987656877)
  ·
    refine ⟨23639165636821203370371329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63037775031523208987656877 23639165636821203370371329)
    ·
      refine ⟨17729374227615902527778497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23639165636821203370371329 17729374227615902527778497)
      ·
        refine ⟨13297030670711926895833873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17729374227615902527778497 13297030670711926895833873)
        ·
          refine ⟨9972773003033945171875405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13297030670711926895833873 9972773003033945171875405)
          ·
            refine ⟨3739789876137729439453277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9972773003033945171875405 3739789876137729439453277)
            ·
              refine ⟨1402421203551648539794979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3739789876137729439453277 1402421203551648539794979)
              ·
                refine ⟨2103631805327472809692469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402421203551648539794979 2103631805327472809692469)
                ·
                  refine ⟨197215481749450575908669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103631805327472809692469 197215481749450575908669)
                  ·
                    rfl

theorem cell22_1728341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_1728341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728341 prefixEnd_1728341 := by exact prefixLift 1728341
  have htrace : WordTrace (prefixWord ++ tailWord_1728341) baseStart_1728341 baseEnd_1728341 := by
    simpa [prefixWord, tailWord_1728341, baseEnd_1728341] using wordTrace_append hprefix tailTrace_1728341
  have hstable : (prefixWord ++ tailWord_1728341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728341).length < 2 ^ (prefixWord ++ tailWord_1728341).sum := by decide
  have hdescent : baseEnd_1728341 < baseStart_1728341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728362 : List Nat := [3, 1, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1728362 : Nat := 118140960795 + 1728362 * 2 ^ 59
def prefixEnd_1728362 : Nat := 4983230072969 + 3 ^ 40 * 1728362 * 2
def baseEnd_1728362 : Nat := 591653633977514672950943

theorem tailTrace_1728362 : CollatzResearch.WordTrace tailWord_1728362 prefixEnd_1728362 591653633977514672950943 := by
  unfold tailWord_1728362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15759635241111782393542835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42025693976298086382780893 15759635241111782393542835)
  ·
    refine ⟨23639452861667673590314253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15759635241111782393542835 23639452861667673590314253)
    ·
      refine ⟨8864794823125377596367845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23639452861667673590314253 8864794823125377596367845)
      ·
        refine ⟨1662149029336008299318971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8864794823125377596367845 1662149029336008299318971)
        ·
          refine ⟨2493223544004012448978457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662149029336008299318971 2493223544004012448978457)
          ·
            refine ⟨1869917658003009336733843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2493223544004012448978457 1869917658003009336733843)
            ·
              refine ⟨2804876487004514005100765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869917658003009336733843 2804876487004514005100765)
              ·
                refine ⟨1051828682626692751912787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2804876487004514005100765 1051828682626692751912787)
                ·
                  refine ⟨1577743023940039127869181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051828682626692751912787 1577743023940039127869181)
                  ·
                    refine ⟨591653633977514672950943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577743023940039127869181 591653633977514672950943)
                    ·
                      rfl

theorem cell22_1728362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1728362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728362 prefixEnd_1728362 := by exact prefixLift 1728362
  have htrace : WordTrace (prefixWord ++ tailWord_1728362) baseStart_1728362 baseEnd_1728362 := by
    simpa [prefixWord, tailWord_1728362, baseEnd_1728362] using wordTrace_append hprefix tailTrace_1728362
  have hstable : (prefixWord ++ tailWord_1728362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728362).length < 2 ^ (prefixWord ++ tailWord_1728362).sum := by decide
  have hdescent : baseEnd_1728362 < baseStart_1728362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728384 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 4, 3]
def baseStart_1728384 : Nat := 118140960795 + 1728384 * 2 ^ 59
def prefixEnd_1728384 : Nat := 4983230072969 + 3 ^ 40 * 1728384 * 2
def baseEnd_1728384 : Nat := 591661165027113948900875

theorem tailTrace_1728384 : CollatzResearch.WordTrace tailWord_1728384 prefixEnd_1728384 591661165027113948900875 := by
  unfold tailWord_1728384
  simp only [CollatzResearch.WordTrace]
  refine ⟨31519671685183713665736103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42026228913578284887648137 31519671685183713665736103)
  ·
    refine ⟨47279507527775570498604155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31519671685183713665736103 47279507527775570498604155)
    ·
      refine ⟨70919261291663355747906233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47279507527775570498604155 70919261291663355747906233)
      ·
        refine ⟨53189445968747516810929675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70919261291663355747906233 53189445968747516810929675)
        ·
          refine ⟨79784168953121275216394513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53189445968747516810929675 79784168953121275216394513)
          ·
            refine ⟨59838126714840956412295885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79784168953121275216394513 59838126714840956412295885)
            ·
              refine ⟨22439297518065358654610957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59838126714840956412295885 22439297518065358654610957)
              ·
                refine ⟨8414736569274509495479109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22439297518065358654610957 8414736569274509495479109)
                ·
                  refine ⟨1577763106738970530402333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8414736569274509495479109 1577763106738970530402333)
                  ·
                    refine ⟨591661165027113948900875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577763106738970530402333 591661165027113948900875)
                    ·
                      rfl

theorem cell22_1728384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_1728384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728384 prefixEnd_1728384 := by exact prefixLift 1728384
  have htrace : WordTrace (prefixWord ++ tailWord_1728384) baseStart_1728384 baseEnd_1728384 := by
    simpa [prefixWord, tailWord_1728384, baseEnd_1728384] using wordTrace_append hprefix tailTrace_1728384
  have hstable : (prefixWord ++ tailWord_1728384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728384).length < 2 ^ (prefixWord ++ tailWord_1728384).sum := by decide
  have hdescent : baseEnd_1728384 < baseStart_1728384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728427 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 8]
def baseStart_1728427 : Nat := 118140960795 + 1728427 * 2 ^ 59
def prefixEnd_1728427 : Nat := 4983230072969 + 3 ^ 40 * 1728427 * 2
def baseEnd_1728427 : Nat := 591675884805876170075743

theorem tailTrace_1728427 : CollatzResearch.WordTrace tailWord_1728427 prefixEnd_1728427 591675884805876170075743 := by
  unfold tailWord_1728427
  simp only [CollatzResearch.WordTrace]
  refine ⟨63040911709211645675287535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42027274472807763783525023 63040911709211645675287535)
  ·
    refine ⟨94561367563817468512931303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63040911709211645675287535 94561367563817468512931303)
    ·
      refine ⟨141842051345726202769396955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94561367563817468512931303 141842051345726202769396955)
      ·
        refine ⟨212763077018589304154095433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141842051345726202769396955 212763077018589304154095433)
        ·
          refine ⟨159572307763941978115571575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212763077018589304154095433 159572307763941978115571575)
          ·
            refine ⟨239358461645912967173357363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159572307763941978115571575 239358461645912967173357363)
            ·
              refine ⟨359037692468869450760036045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239358461645912967173357363 359037692468869450760036045)
              ·
                refine ⟨134639134675826044035013517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359037692468869450760036045 134639134675826044035013517)
                ·
                  refine ⟨50489675503434766513130069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134639134675826044035013517 50489675503434766513130069)
                  ·
                    refine ⟨591675884805876170075743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50489675503434766513130069 591675884805876170075743)
                    ·
                      rfl

theorem cell22_1728427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_1728427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728427 prefixEnd_1728427 := by exact prefixLift 1728427
  have htrace : WordTrace (prefixWord ++ tailWord_1728427) baseStart_1728427 baseEnd_1728427 := by
    simpa [prefixWord, tailWord_1728427, baseEnd_1728427] using wordTrace_append hprefix tailTrace_1728427
  have hstable : (prefixWord ++ tailWord_1728427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728427).length < 2 ^ (prefixWord ++ tailWord_1728427).sum := by decide
  have hdescent : baseEnd_1728427 < baseStart_1728427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728459 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 5]
def baseStart_1728459 : Nat := 118140960795 + 1728459 * 2 ^ 59
def prefixEnd_1728459 : Nat := 4983230072969 + 3 ^ 40 * 1728459 * 2
def baseEnd_1728459 : Nat := 197228946353279584425215

theorem tailTrace_1728459 : CollatzResearch.WordTrace tailWord_1728459 prefixEnd_1728459 197228946353279584425215 := by
  unfold tailWord_1728459
  simp only [CollatzResearch.WordTrace]
  refine ⟨63042078845095715140452431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42028052563397143426968287 63042078845095715140452431)
  ·
    refine ⟨94563118267643572710678647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63042078845095715140452431 94563118267643572710678647)
    ·
      refine ⟨141844677401465359066017971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94563118267643572710678647 141844677401465359066017971)
      ·
        refine ⟨212767016102198038599026957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141844677401465359066017971 212767016102198038599026957)
        ·
          refine ⟨79787631038324264474635109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212767016102198038599026957 79787631038324264474635109)
          ·
            refine ⟨14960180819685799588994083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79787631038324264474635109 14960180819685799588994083)
            ·
              refine ⟨22440271229528699383491125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14960180819685799588994083 22440271229528699383491125)
              ·
                refine ⟨2103775427768315567202293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22440271229528699383491125 2103775427768315567202293)
                ·
                  refine ⟨197228946353279584425215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103775427768315567202293 197228946353279584425215)
                  ·
                    rfl

theorem cell22_1728459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 5].length) (baseStart_1728459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728459 prefixEnd_1728459 := by exact prefixLift 1728459
  have htrace : WordTrace (prefixWord ++ tailWord_1728459) baseStart_1728459 baseEnd_1728459 := by
    simpa [prefixWord, tailWord_1728459, baseEnd_1728459] using wordTrace_append hprefix tailTrace_1728459
  have hstable : (prefixWord ++ tailWord_1728459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728459).length < 2 ^ (prefixWord ++ tailWord_1728459).sum := by decide
  have hdescent : baseEnd_1728459 < baseStart_1728459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728493 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1728493 : Nat := 118140960795 + 1728493 * 2 ^ 59
def prefixEnd_1728493 : Nat := 4983230072969 + 3 ^ 40 * 1728493 * 2
def baseEnd_1728493 : Nat := 197232825984891332641847

theorem tailTrace_1728493 : CollatzResearch.WordTrace tailWord_1728493 prefixEnd_1728493 197232825984891332641847 := by
  unfold tailWord_1728493
  simp only [CollatzResearch.WordTrace]
  refine ⟨63043318926972538947190133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42028879284648359298126755 63043318926972538947190133)
  ·
    refine ⟨5910311149403675526299075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63043318926972538947190133 5910311149403675526299075)
    ·
      refine ⟨8865466724105513289448613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910311149403675526299075 8865466724105513289448613)
      ·
        refine ⟨1662275010769783741771615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8865466724105513289448613 1662275010769783741771615)
        ·
          refine ⟨2493412516154675612657423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662275010769783741771615 2493412516154675612657423)
          ·
            refine ⟨3740118774232013418986135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493412516154675612657423 3740118774232013418986135)
            ·
              refine ⟨5610178161348020128479203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740118774232013418986135 5610178161348020128479203)
              ·
                refine ⟨8415267242022030192718805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610178161348020128479203 8415267242022030192718805)
                ·
                  refine ⟨197232825984891332641847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8415267242022030192718805 197232825984891332641847)
                  ·
                    rfl

theorem cell22_1728493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1728493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728493 prefixEnd_1728493 := by exact prefixLift 1728493
  have htrace : WordTrace (prefixWord ++ tailWord_1728493) baseStart_1728493 baseEnd_1728493 := by
    simpa [prefixWord, tailWord_1728493, baseEnd_1728493] using wordTrace_append hprefix tailTrace_1728493
  have hstable : (prefixWord ++ tailWord_1728493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728493).length < 2 ^ (prefixWord ++ tailWord_1728493).sum := by decide
  have hdescent : baseEnd_1728493 < baseStart_1728493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728504 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 6]
def baseStart_1728504 : Nat := 118140960795 + 1728504 * 2 ^ 59
def prefixEnd_1728504 : Nat := 4983230072969 + 3 ^ 40 * 1728504 * 2
def baseEnd_1728504 : Nat := 197234081159824545300169

theorem tailTrace_1728504 : CollatzResearch.WordTrace tailWord_1728504 prefixEnd_1728504 197234081159824545300169 := by
  unfold tailWord_1728504
  simp only [CollatzResearch.WordTrace]
  refine ⟨31521860064966343912920283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42029146753288458550560377 31521860064966343912920283)
  ·
    refine ⟨47282790097449515869380425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31521860064966343912920283 47282790097449515869380425)
    ·
      refine ⟨35462092573087136902035319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47282790097449515869380425 35462092573087136902035319)
      ·
        refine ⟨53193138859630705353052979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35462092573087136902035319 53193138859630705353052979)
        ·
          refine ⟨79789708289446058029579469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53193138859630705353052979 79789708289446058029579469)
          ·
            refine ⟨29921140608542271761092301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79789708289446058029579469 29921140608542271761092301)
            ·
              refine ⟨11220427728203351910409613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29921140608542271761092301 11220427728203351910409613)
              ·
                refine ⟨4207660398076256966403605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11220427728203351910409613 4207660398076256966403605)
                ·
                  refine ⟨197234081159824545300169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4207660398076256966403605 197234081159824545300169)
                  ·
                    rfl

theorem cell22_1728504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_1728504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728504 prefixEnd_1728504 := by exact prefixLift 1728504
  have htrace : WordTrace (prefixWord ++ tailWord_1728504) baseStart_1728504 baseEnd_1728504 := by
    simpa [prefixWord, tailWord_1728504, baseEnd_1728504] using wordTrace_append hprefix tailTrace_1728504
  have hstable : (prefixWord ++ tailWord_1728504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728504).length < 2 ^ (prefixWord ++ tailWord_1728504).sum := by decide
  have hdescent : baseEnd_1728504 < baseStart_1728504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728510 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1728510 : Nat := 118140960795 + 1728510 * 2 ^ 59
def prefixEnd_1728510 : Nat := 4983230072969 + 3 ^ 40 * 1728510 * 2
def baseEnd_1728510 : Nat := 197234765800697206750163

theorem tailTrace_1728510 : CollatzResearch.WordTrace tailWord_1728510 prefixEnd_1728510 197234765800697206750163 := by
  unfold tailWord_1728510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880492370988868856319873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42029292645273967233705989 7880492370988868856319873)
  ·
    refine ⟨5910369278241651642239905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7880492370988868856319873 5910369278241651642239905)
    ·
      refine ⟨4432776958681238731679929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5910369278241651642239905 4432776958681238731679929)
      ·
        refine ⟨3324582719010929048759947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4432776958681238731679929 3324582719010929048759947)
        ·
          refine ⟨4986874078516393573139921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324582719010929048759947 4986874078516393573139921)
          ·
            refine ⟨3740155558887295179854941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4986874078516393573139921 3740155558887295179854941)
            ·
              refine ⟨1402558334582735692445603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3740155558887295179854941 1402558334582735692445603)
              ·
                refine ⟨2103837501874103538668405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402558334582735692445603 2103837501874103538668405)
                ·
                  refine ⟨197234765800697206750163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103837501874103538668405 197234765800697206750163)
                  ·
                    rfl

theorem cell22_1728510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1728510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728510 prefixEnd_1728510 := by exact prefixLift 1728510
  have htrace : WordTrace (prefixWord ++ tailWord_1728510) baseStart_1728510 baseEnd_1728510 := by
    simpa [prefixWord, tailWord_1728510, baseEnd_1728510] using wordTrace_append hprefix tailTrace_1728510
  have hstable : (prefixWord ++ tailWord_1728510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728510).length < 2 ^ (prefixWord ++ tailWord_1728510).sum := by decide
  have hdescent : baseEnd_1728510 < baseStart_1728510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728536 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 6, 3]
def baseStart_1728536 : Nat := 118140960795 + 1728536 * 2 ^ 59
def prefixEnd_1728536 : Nat := 4983230072969 + 3 ^ 40 * 1728536 * 2
def baseEnd_1728536 : Nat := 591713197733436219100409

theorem tailTrace_1728536 : CollatzResearch.WordTrace tailWord_1728536 prefixEnd_1728536 591713197733436219100409 := by
  unfold tailWord_1728536
  simp only [CollatzResearch.WordTrace]
  refine ⟨31522443632908378645502731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42029924843877838194003641 31522443632908378645502731)
  ·
    refine ⟨47283665449362567968254097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31522443632908378645502731 47283665449362567968254097)
    ·
      refine ⟨35462749087021925976190573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47283665449362567968254097 35462749087021925976190573)
      ·
        refine ⟨13298530907633222241071465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35462749087021925976190573 13298530907633222241071465)
        ·
          refine ⟨9973898180724916680803599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13298530907633222241071465 9973898180724916680803599)
          ·
            refine ⟨14960847271087375021205399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9973898180724916680803599 14960847271087375021205399)
            ·
              refine ⟨22441270906631062531808099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14960847271087375021205399 22441270906631062531808099)
              ·
                refine ⟨33661906359946593797712149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22441270906631062531808099 33661906359946593797712149)
                ·
                  refine ⟨1577901860622496584267757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33661906359946593797712149 1577901860622496584267757)
                  ·
                    refine ⟨591713197733436219100409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577901860622496584267757 591713197733436219100409)
                    ·
                      rfl

theorem cell22_1728536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_1728536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728536 prefixEnd_1728536 := by exact prefixLift 1728536
  have htrace : WordTrace (prefixWord ++ tailWord_1728536) baseStart_1728536 baseEnd_1728536 := by
    simpa [prefixWord, tailWord_1728536, baseEnd_1728536] using wordTrace_append hprefix tailTrace_1728536
  have hstable : (prefixWord ++ tailWord_1728536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728536).length < 2 ^ (prefixWord ++ tailWord_1728536).sum := by decide
  have hdescent : baseEnd_1728536 < baseStart_1728536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728538 : List Nat := [3, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_1728538 : Nat := 118140960795 + 1728538 * 2 ^ 59
def prefixEnd_1728538 : Nat := 4983230072969 + 3 ^ 40 * 1728538 * 2
def baseEnd_1728538 : Nat := 197237960791436293516801

theorem tailTrace_1728538 : CollatzResearch.WordTrace tailWord_1728538 prefixEnd_1728538 197237960791436293516801 := by
  unfold tailWord_1728538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15761240052952377908144567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42029973474539674421718845 15761240052952377908144567)
  ·
    refine ⟨23641860079428566862216851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15761240052952377908144567 23641860079428566862216851)
    ·
      refine ⟨35462790119142850293325277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23641860079428566862216851 35462790119142850293325277)
      ·
        refine ⟨13298546294678568859996979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35462790119142850293325277 13298546294678568859996979)
        ·
          refine ⟨19947819442017853289995469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298546294678568859996979 19947819442017853289995469)
          ·
            refine ⟨7480432290756694983748301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19947819442017853289995469 7480432290756694983748301)
            ·
              refine ⟨2805162109033760618905613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7480432290756694983748301 2805162109033760618905613)
              ·
                refine ⟨1051935790887660232089605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2805162109033760618905613 1051935790887660232089605)
                ·
                  refine ⟨197237960791436293516801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051935790887660232089605 197237960791436293516801)
                  ·
                    rfl

theorem cell22_1728538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_1728538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728538 prefixEnd_1728538 := by exact prefixLift 1728538
  have htrace : WordTrace (prefixWord ++ tailWord_1728538) baseStart_1728538 baseEnd_1728538 := by
    simpa [prefixWord, tailWord_1728538, baseEnd_1728538] using wordTrace_append hprefix tailTrace_1728538
  have hstable : (prefixWord ++ tailWord_1728538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728538).length < 2 ^ (prefixWord ++ tailWord_1728538).sum := by decide
  have hdescent : baseEnd_1728538 < baseStart_1728538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728549 : List Nat := [1, 3, 1, 2, 2, 3, 10]
def baseStart_1728549 : Nat := 118140960795 + 1728549 * 2 ^ 59
def prefixEnd_1728549 : Nat := 4983230072969 + 3 ^ 40 * 1728549 * 2
def baseEnd_1728549 : Nat := 21915468440707722908347

theorem tailTrace_1728549 : CollatzResearch.WordTrace tailWord_1728549 prefixEnd_1728549 21915468440707722908347 := by
  unfold tailWord_1728549
  simp only [CollatzResearch.WordTrace]
  refine ⟨63045361414769660511228701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42030240943179773674152467 63045361414769660511228701)
  ·
    refine ⟨23642010530538622691710763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63045361414769660511228701 23642010530538622691710763)
    ·
      refine ⟨35463015795807934037566145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23642010530538622691710763 35463015795807934037566145)
      ·
        refine ⟨26597261846855950528174609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35463015795807934037566145 26597261846855950528174609)
        ·
          refine ⟨19947946385141962896130957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26597261846855950528174609 19947946385141962896130957)
          ·
            refine ⟨7480479894428236086049109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19947946385141962896130957 7480479894428236086049109)
            ·
              refine ⟨21915468440707722908347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7480479894428236086049109 21915468440707722908347)
              ·
                rfl

theorem cell22_1728549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 10].length) (baseStart_1728549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728549 prefixEnd_1728549 := by exact prefixLift 1728549
  have htrace : WordTrace (prefixWord ++ tailWord_1728549) baseStart_1728549 baseEnd_1728549 := by
    simpa [prefixWord, tailWord_1728549, baseEnd_1728549] using wordTrace_append hprefix tailTrace_1728549
  have hstable : (prefixWord ++ tailWord_1728549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728549).length < 2 ^ (prefixWord ++ tailWord_1728549).sum := by decide
  have hdescent : baseEnd_1728549 < baseStart_1728549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728579 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 4, 6]
def baseStart_1728579 : Nat := 118140960795 + 1728579 * 2 ^ 59
def prefixEnd_1728579 : Nat := 4983230072969 + 3 ^ 40 * 1728579 * 2
def baseEnd_1728579 : Nat := 591727917512198440275277

theorem tailTrace_1728579 : CollatzResearch.WordTrace tailWord_1728579 prefixEnd_1728579 591727917512198440275277 := by
  unfold tailWord_1728579
  simp only [CollatzResearch.WordTrace]
  refine ⟨63046455604660975634820791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42030970403107317089880527 63046455604660975634820791)
  ·
    refine ⟨94569683406991463452231187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63046455604660975634820791 94569683406991463452231187)
    ·
      refine ⟨141854525110487195178346781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94569683406991463452231187 141854525110487195178346781)
      ·
        refine ⟨53195446916432698191880043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141854525110487195178346781 53195446916432698191880043)
        ·
          refine ⟨79793170374649047287820065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53195446916432698191880043 79793170374649047287820065)
          ·
            refine ⟨59844877780986785465865049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79793170374649047287820065 59844877780986785465865049)
            ·
              refine ⟨44883658335740089099398787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59844877780986785465865049 44883658335740089099398787)
              ·
                refine ⟨67325487503610133649098181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44883658335740089099398787 67325487503610133649098181)
                ·
                  refine ⟨12623528906926900059205909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67325487503610133649098181 12623528906926900059205909)
                  ·
                    refine ⟨591727917512198440275277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12623528906926900059205909 591727917512198440275277)
                    ·
                      rfl

theorem cell22_1728579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_1728579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728579 prefixEnd_1728579 := by exact prefixLift 1728579
  have htrace : WordTrace (prefixWord ++ tailWord_1728579) baseStart_1728579 baseEnd_1728579 := by
    simpa [prefixWord, tailWord_1728579, baseEnd_1728579] using wordTrace_append hprefix tailTrace_1728579
  have hstable : (prefixWord ++ tailWord_1728579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728579).length < 2 ^ (prefixWord ++ tailWord_1728579).sum := by decide
  have hdescent : baseEnd_1728579 < baseStart_1728579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728581 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_1728581 : Nat := 118140960795 + 1728581 * 2 ^ 59
def prefixEnd_1728581 : Nat := 4983230072969 + 3 ^ 40 * 1728581 * 2
def baseEnd_1728581 : Nat := 591728602153071101725271

theorem tailTrace_1728581 : CollatzResearch.WordTrace tailWord_1728581 prefixEnd_1728581 591728602153071101725271 := by
  unfold tailWord_1728581
  simp only [CollatzResearch.WordTrace]
  refine ⟨63046528550653729976393597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42031019033769153317595731 63046528550653729976393597)
  ·
    refine ⟨23642448206495148741147599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63046528550653729976393597 23642448206495148741147599)
    ·
      refine ⟨35463672309742723111721399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23642448206495148741147599 35463672309742723111721399)
      ·
        refine ⟨53195508464614084667582099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35463672309742723111721399 53195508464614084667582099)
        ·
          refine ⟨79793262696921127001373149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53195508464614084667582099 79793262696921127001373149)
          ·
            refine ⟨29922473511345422625514931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79793262696921127001373149 29922473511345422625514931)
            ·
              refine ⟨44883710267018133938272397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29922473511345422625514931 44883710267018133938272397)
              ·
                refine ⟨16831391350131800226852149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44883710267018133938272397 16831391350131800226852149)
                ·
                  refine ⟨1577942939074856271267389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16831391350131800226852149 1577942939074856271267389)
                  ·
                    refine ⟨591728602153071101725271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577942939074856271267389 591728602153071101725271)
                    ·
                      rfl

theorem cell22_1728581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_1728581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728581 prefixEnd_1728581 := by exact prefixLift 1728581
  have htrace : WordTrace (prefixWord ++ tailWord_1728581) baseStart_1728581 baseEnd_1728581 := by
    simpa [prefixWord, tailWord_1728581, baseEnd_1728581] using wordTrace_append hprefix tailTrace_1728581
  have hstable : (prefixWord ++ tailWord_1728581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728581).length < 2 ^ (prefixWord ++ tailWord_1728581).sum := by decide
  have hdescent : baseEnd_1728581 < baseStart_1728581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728606 : List Nat := [4, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1728606 : Nat := 118140960795 + 1728606 * 2 ^ 59
def prefixEnd_1728606 : Nat := 4983230072969 + 3 ^ 40 * 1728606 * 2
def baseEnd_1728606 : Nat := 197245720054659789950065

theorem tailTrace_1728606 : CollatzResearch.WordTrace tailWord_1728606 prefixEnd_1728606 197245720054659789950065 := by
  unfold tailWord_1728606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880930046945394905756709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42031626917042106164035781 7880930046945394905756709)
  ·
    refine ⟨1477674383802261544829383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7880930046945394905756709 1477674383802261544829383)
    ·
      refine ⟨2216511575703392317244075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477674383802261544829383 2216511575703392317244075)
      ·
        refine ⟨3324767363555088475866113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216511575703392317244075 3324767363555088475866113)
        ·
          refine ⟨2493575522666316356899585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324767363555088475866113 2493575522666316356899585)
          ·
            refine ⟨1870181641999737267674689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2493575522666316356899585 1870181641999737267674689)
            ·
              refine ⟨1402636231499802950756017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870181641999737267674689 1402636231499802950756017)
              ·
                refine ⟨1051977173624852213067013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402636231499802950756017 1051977173624852213067013)
                ·
                  refine ⟨197245720054659789950065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051977173624852213067013 197245720054659789950065)
                  ·
                    rfl

theorem cell22_1728606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1728606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728606 prefixEnd_1728606 := by exact prefixLift 1728606
  have htrace : WordTrace (prefixWord ++ tailWord_1728606) baseStart_1728606 baseEnd_1728606 := by
    simpa [prefixWord, tailWord_1728606, baseEnd_1728606] using wordTrace_append hprefix tailTrace_1728606
  have hstable : (prefixWord ++ tailWord_1728606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728606).length < 2 ^ (prefixWord ++ tailWord_1728606).sum := by decide
  have hdescent : baseEnd_1728606 < baseStart_1728606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728611 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 5]
def baseStart_1728611 : Nat := 118140960795 + 1728611 * 2 ^ 59
def prefixEnd_1728611 : Nat := 4983230072969 + 3 ^ 40 * 1728611 * 2
def baseEnd_1728611 : Nat := 197246290588720341158393

theorem tailTrace_1728611 : CollatzResearch.WordTrace tailWord_1728611 prefixEnd_1728611 197246290588720341158393 := by
  unfold tailWord_1728611
  simp only [CollatzResearch.WordTrace]
  refine ⟨63047622740545045099985687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42031748493696696733323791 63047622740545045099985687)
  ·
    refine ⟨94571434110817567649978531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63047622740545045099985687 94571434110817567649978531)
    ·
      refine ⟨141857151166226351474967797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94571434110817567649978531 141857151166226351474967797)
      ·
        refine ⟨13299107921833720450778231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141857151166226351474967797 13299107921833720450778231)
        ·
          refine ⟨19948661882750580676167347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13299107921833720450778231 19948661882750580676167347)
          ·
            refine ⟨29922992824125871014251021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19948661882750580676167347 29922992824125871014251021)
            ·
              refine ⟨11221122309047201630344133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29922992824125871014251021 11221122309047201630344133)
              ·
                refine ⟨2103960432946350305689525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11221122309047201630344133 2103960432946350305689525)
                ·
                  refine ⟨197246290588720341158393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103960432946350305689525 197246290588720341158393)
                  ·
                    rfl

theorem cell22_1728611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 5].length) (baseStart_1728611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728611 prefixEnd_1728611 := by exact prefixLift 1728611
  have htrace : WordTrace (prefixWord ++ tailWord_1728611) baseStart_1728611 baseEnd_1728611 := by
    simpa [prefixWord, tailWord_1728611, baseEnd_1728611] using wordTrace_append hprefix tailTrace_1728611
  have hstable : (prefixWord ++ tailWord_1728611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728611).length < 2 ^ (prefixWord ++ tailWord_1728611).sum := by decide
  have hdescent : baseEnd_1728611 < baseStart_1728611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728615 : List Nat := [1, 1, 5, 1, 1, 2, 3, 4, 1, 3]
def baseStart_1728615 : Nat := 118140960795 + 1728615 * 2 ^ 59
def prefixEnd_1728615 : Nat := 4983230072969 + 3 ^ 40 * 1728615 * 2
def baseEnd_1728615 : Nat := 591740241047906346375167

theorem tailTrace_1728615 : CollatzResearch.WordTrace tailWord_1728615 prefixEnd_1728615 591740241047906346375167 := by
  unfold tailWord_1728615
  simp only [CollatzResearch.WordTrace]
  refine ⟨63047768632530553783131299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42031845755020369188754199 63047768632530553783131299)
  ·
    refine ⟨94571652948795830674696949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63047768632530553783131299 94571652948795830674696949)
    ·
      refine ⟨8866092463949609125752839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94571652948795830674696949 8866092463949609125752839)
      ·
        refine ⟨13299138695924413688629259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8866092463949609125752839 13299138695924413688629259)
        ·
          refine ⟨19948708043886620532943889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13299138695924413688629259 19948708043886620532943889)
          ·
            refine ⟨14961531032914965399707917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19948708043886620532943889 14961531032914965399707917)
            ·
              refine ⟨5610574137343112024890469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14961531032914965399707917 5610574137343112024890469)
              ·
                refine ⟨1051982650751833504666963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5610574137343112024890469 1051982650751833504666963)
                ·
                  refine ⟨1577973976127750257000445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051982650751833504666963 1577973976127750257000445)
                  ·
                    refine ⟨591740241047906346375167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577973976127750257000445 591740241047906346375167)
                    ·
                      rfl

theorem cell22_1728615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_1728615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728615 prefixEnd_1728615 := by exact prefixLift 1728615
  have htrace : WordTrace (prefixWord ++ tailWord_1728615) baseStart_1728615 baseEnd_1728615 := by
    simpa [prefixWord, tailWord_1728615, baseEnd_1728615] using wordTrace_append hprefix tailTrace_1728615
  have hstable : (prefixWord ++ tailWord_1728615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728615).length < 2 ^ (prefixWord ++ tailWord_1728615).sum := by decide
  have hdescent : baseEnd_1728615 < baseStart_1728615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728626 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1728626 : Nat := 118140960795 + 1728626 * 2 ^ 59
def prefixEnd_1728626 : Nat := 4983230072969 + 3 ^ 40 * 1728626 * 2
def baseEnd_1728626 : Nat := 591744006572705984350133

theorem tailTrace_1728626 : CollatzResearch.WordTrace tailWord_1728626 prefixEnd_1728626 591744006572705984350133 := by
  unfold tailWord_1728626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15762042458872675665445433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42032113223660468441187821 15762042458872675665445433)
  ·
    refine ⟨11821531844154506749084075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15762042458872675665445433 11821531844154506749084075)
    ·
      refine ⟨17732297766231760123626113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11821531844154506749084075 17732297766231760123626113)
      ·
        refine ⟨13299223324673820092719585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17732297766231760123626113 13299223324673820092719585)
        ·
          refine ⟨9974417493505365069539689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13299223324673820092719585 9974417493505365069539689)
          ·
            refine ⟨7480813120129023802154767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9974417493505365069539689 7480813120129023802154767)
            ·
              refine ⟨11221219680193535703232151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7480813120129023802154767 11221219680193535703232151)
              ·
                refine ⟨16831829520290303554848227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11221219680193535703232151 16831829520290303554848227)
                ·
                  refine ⟨25247744280435455332272341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16831829520290303554848227 25247744280435455332272341)
                  ·
                    refine ⟨591744006572705984350133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25247744280435455332272341 591744006572705984350133)
                    ·
                      rfl

theorem cell22_1728626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1728626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728626 prefixEnd_1728626 := by exact prefixLift 1728626
  have htrace : WordTrace (prefixWord ++ tailWord_1728626) baseStart_1728626 baseEnd_1728626 := by
    simpa [prefixWord, tailWord_1728626, baseEnd_1728626] using wordTrace_append hprefix tailTrace_1728626
  have hstable : (prefixWord ++ tailWord_1728626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728626).length < 2 ^ (prefixWord ++ tailWord_1728626).sum := by decide
  have hdescent : baseEnd_1728626 < baseStart_1728626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728673 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 6]
def baseStart_1728673 : Nat := 118140960795 + 1728673 * 2 ^ 59
def prefixEnd_1728673 : Nat := 4983230072969 + 3 ^ 40 * 1728673 * 2
def baseEnd_1728673 : Nat := 197253365211071176141663

theorem tailTrace_1728673 : CollatzResearch.WordTrace tailWord_1728673 prefixEnd_1728673 197253365211071176141663 := by
  unfold tailWord_1728673
  simp only [CollatzResearch.WordTrace]
  refine ⟨63049884066320429688742673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42033256044213619792495115 63049884066320429688742673)
  ·
    refine ⟨47287413049740322266557005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63049884066320429688742673 47287413049740322266557005)
    ·
      refine ⟨17732779893652620849958877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47287413049740322266557005 17732779893652620849958877)
      ·
        refine ⟨6649792460119732818734579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17732779893652620849958877 6649792460119732818734579)
        ·
          refine ⟨9974688690179599228101869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6649792460119732818734579 9974688690179599228101869)
          ·
            refine ⟨3740508258817349710538201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9974688690179599228101869 3740508258817349710538201)
            ·
              refine ⟨2805381194113012282903651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3740508258817349710538201 2805381194113012282903651)
              ·
                refine ⟨4208071791169518424355477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805381194113012282903651 4208071791169518424355477)
                ·
                  refine ⟨197253365211071176141663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4208071791169518424355477 197253365211071176141663)
                  ·
                    rfl

theorem cell22_1728673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_1728673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728673 prefixEnd_1728673 := by exact prefixLift 1728673
  have htrace : WordTrace (prefixWord ++ tailWord_1728673) baseStart_1728673 baseEnd_1728673 := by
    simpa [prefixWord, tailWord_1728673, baseEnd_1728673] using wordTrace_append hprefix tailTrace_1728673
  have hstable : (prefixWord ++ tailWord_1728673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728673).length < 2 ^ (prefixWord ++ tailWord_1728673).sum := by decide
  have hdescent : baseEnd_1728673 < baseStart_1728673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728718 : List Nat := [4, 1, 1, 1, 4, 3, 8]
def baseStart_1728718 : Nat := 118140960795 + 1728718 * 2 ^ 59
def prefixEnd_1728718 : Nat := 4983230072969 + 3 ^ 40 * 1728718 * 2
def baseEnd_1728718 : Nat := 21917611113068459668513

theorem tailTrace_1728718 : CollatzResearch.WordTrace tailWord_1728718 prefixEnd_1728718 21917611113068459668513 := by
  unfold tailWord_1728718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881440668894675296766351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42034350234104934916087205 7881440668894675296766351)
  ·
    refine ⟨11822161003342012945149527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7881440668894675296766351 11822161003342012945149527)
    ·
      refine ⟨17733241505013019417724291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11822161003342012945149527 17733241505013019417724291)
      ·
        refine ⟨26599862257519529126586437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17733241505013019417724291 26599862257519529126586437)
        ·
          refine ⟨4987474173284911711234957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26599862257519529126586437 4987474173284911711234957)
          ·
            refine ⟨1870302814981841891713109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4987474173284911711234957 1870302814981841891713109)
            ·
              refine ⟨21917611113068459668513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1870302814981841891713109 21917611113068459668513)
              ·
                rfl

theorem cell22_1728718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 8].length) (baseStart_1728718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728718 prefixEnd_1728718 := by exact prefixLift 1728718
  have htrace : WordTrace (prefixWord ++ tailWord_1728718) baseStart_1728718 baseEnd_1728718 := by
    simpa [prefixWord, tailWord_1728718, baseEnd_1728718] using wordTrace_append hprefix tailTrace_1728718
  have hstable : (prefixWord ++ tailWord_1728718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728718).length < 2 ^ (prefixWord ++ tailWord_1728718).sum := by decide
  have hdescent : baseEnd_1728718 < baseStart_1728718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728761 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_1728761 : Nat := 118140960795 + 1728761 * 2 ^ 59
def prefixEnd_1728761 : Nat := 4983230072969 + 3 ^ 40 * 1728761 * 2
def baseEnd_1728761 : Nat := 591790219831610632224719

theorem tailTrace_1728761 : CollatzResearch.WordTrace tailWord_1728761 prefixEnd_1728761 591790219831610632224719 := by
  unfold tailWord_1728761
  simp only [CollatzResearch.WordTrace]
  refine ⟨63053093690001620717946137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42035395793334413811964091 63053093690001620717946137)
  ·
    refine ⟨47289820267501215538459603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63053093690001620717946137 47289820267501215538459603)
    ·
      refine ⟨70934730401251823307689405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47289820267501215538459603 70934730401251823307689405)
      ·
        refine ⟨26600523900469433740383527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70934730401251823307689405 26600523900469433740383527)
        ·
          refine ⟨39900785850704150610575291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26600523900469433740383527 39900785850704150610575291)
          ·
            refine ⟨59851178776056225915862937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39900785850704150610575291 59851178776056225915862937)
            ·
              refine ⟨44888384082042169436897203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59851178776056225915862937 44888384082042169436897203)
              ·
                refine ⟨67332576123063254155345805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44888384082042169436897203 67332576123063254155345805)
                ·
                  refine ⟨25249716046148720308254677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67332576123063254155345805 25249716046148720308254677)
                  ·
                    refine ⟨591790219831610632224719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25249716046148720308254677 591790219831610632224719)
                    ·
                      rfl

theorem cell22_1728761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_1728761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728761 prefixEnd_1728761 := by exact prefixLift 1728761
  have htrace : WordTrace (prefixWord ++ tailWord_1728761) baseStart_1728761 baseEnd_1728761 := by
    simpa [prefixWord, tailWord_1728761, baseEnd_1728761] using wordTrace_append hprefix tailTrace_1728761
  have hstable : (prefixWord ++ tailWord_1728761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728761).length < 2 ^ (prefixWord ++ tailWord_1728761).sum := by decide
  have hdescent : baseEnd_1728761 < baseStart_1728761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728868 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1728868 : Nat := 118140960795 + 1728868 * 2 ^ 59
def prefixEnd_1728868 : Nat := 4983230072969 + 3 ^ 40 * 1728868 * 2
def baseEnd_1728868 : Nat := 591826848118298019799391

theorem tailTrace_1728868 : CollatzResearch.WordTrace tailWord_1728868 prefixEnd_1728868 591826848118298019799391 := by
  unfold tailWord_1728868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31528498150306988996045629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42037997533742651994727505 31528498150306988996045629)
  ·
    refine ⟨11823186806365120873517111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31528498150306988996045629 11823186806365120873517111)
    ·
      refine ⟨17734780209547681310275667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823186806365120873517111 17734780209547681310275667)
      ·
        refine ⟨26602170314321521965413501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17734780209547681310275667 26602170314321521965413501)
        ·
          refine ⟨9975813867870570737030063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26602170314321521965413501 9975813867870570737030063)
          ·
            refine ⟨14963720801805856105545095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9975813867870570737030063 14963720801805856105545095)
            ·
              refine ⟨22445581202708784158317643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14963720801805856105545095 22445581202708784158317643)
              ·
                refine ⟨33668371804063176237476465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22445581202708784158317643 33668371804063176237476465)
                ·
                  refine ⟨25251278853047382178107349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33668371804063176237476465 25251278853047382178107349)
                  ·
                    refine ⟨591826848118298019799391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25251278853047382178107349 591826848118298019799391)
                    ·
                      rfl

theorem cell22_1728868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1728868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728868 prefixEnd_1728868 := by exact prefixLift 1728868
  have htrace : WordTrace (prefixWord ++ tailWord_1728868) baseStart_1728868 baseEnd_1728868 := by
    simpa [prefixWord, tailWord_1728868, baseEnd_1728868] using wordTrace_append hprefix tailTrace_1728868
  have hstable : (prefixWord ++ tailWord_1728868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728868).length < 2 ^ (prefixWord ++ tailWord_1728868).sum := by decide
  have hdescent : baseEnd_1728868 < baseStart_1728868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1728975 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 6, 3]
def baseStart_1728975 : Nat := 118140960795 + 1728975 * 2 ^ 59
def prefixEnd_1728975 : Nat := 4983230072969 + 3 ^ 40 * 1728975 * 2
def baseEnd_1728975 : Nat := 591863476404985407374063

theorem tailTrace_1728975 : CollatzResearch.WordTrace tailWord_1728975 prefixEnd_1728975 591863476404985407374063 := by
  unfold tailWord_1728975
  simp only [CollatzResearch.WordTrace]
  refine ⟨63060898911226335266236379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42040599274150890177490919 63060898911226335266236379)
  ·
    refine ⟨94591348366839502899354569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63060898911226335266236379 94591348366839502899354569)
    ·
      refine ⟨70943511275129627174515927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94591348366839502899354569 70943511275129627174515927)
      ·
        refine ⟨106415266912694440761773891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70943511275129627174515927 106415266912694440761773891)
        ·
          refine ⟨159622900369041661142660837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106415266912694440761773891 159622900369041661142660837)
          ·
            refine ⟨29929293819195311464248907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159622900369041661142660837 29929293819195311464248907)
            ·
              refine ⟨44893940728792967196373361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29929293819195311464248907 44893940728792967196373361)
              ·
                refine ⟨33670455546594725397280021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44893940728792967196373361 33670455546594725397280021)
                ·
                  refine ⟨1578302603746627752997501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33670455546594725397280021 1578302603746627752997501)
                  ·
                    refine ⟨591863476404985407374063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1578302603746627752997501 591863476404985407374063)
                    ·
                      rfl

theorem cell22_1728975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_1728975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1728975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1728975 prefixEnd_1728975 := by exact prefixLift 1728975
  have htrace : WordTrace (prefixWord ++ tailWord_1728975) baseStart_1728975 baseEnd_1728975 := by
    simpa [prefixWord, tailWord_1728975, baseEnd_1728975] using wordTrace_append hprefix tailTrace_1728975
  have hstable : (prefixWord ++ tailWord_1728975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1728975).length < 2 ^ (prefixWord ++ tailWord_1728975).sum := by decide
  have hdescent : baseEnd_1728975 < baseStart_1728975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1728975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729026 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1729026 : Nat := 118140960795 + 1729026 * 2 ^ 59
def prefixEnd_1729026 : Nat := 4983230072969 + 3 ^ 40 * 1729026 * 2
def baseEnd_1729026 : Nat := 591880934747238274348907

theorem tailTrace_1729026 : CollatzResearch.WordTrace tailWord_1729026 prefixEnd_1729026 591880934747238274348907 := by
  unfold tailWord_1729026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765689758510392744085733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42041839356027713984228621 15765689758510392744085733)
  ·
    refine ⟨2956066829720698639516075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15765689758510392744085733 2956066829720698639516075)
    ·
      refine ⟨4434100244581047959274113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956066829720698639516075 4434100244581047959274113)
      ·
        refine ⟨3325575183435785969455585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4434100244581047959274113 3325575183435785969455585)
        ·
          refine ⟨2494181387576839477091689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3325575183435785969455585 2494181387576839477091689)
          ·
            refine ⟨1870636040682629607818767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494181387576839477091689 1870636040682629607818767)
            ·
              refine ⟨2805954061023944411728151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870636040682629607818767 2805954061023944411728151)
              ·
                refine ⟨4208931091535916617592227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805954061023944411728151 4208931091535916617592227)
                ·
                  refine ⟨6313396637303874926388341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208931091535916617592227 6313396637303874926388341)
                  ·
                    refine ⟨591880934747238274348907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6313396637303874926388341 591880934747238274348907)
                    ·
                      rfl

theorem cell22_1729026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1729026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729026 prefixEnd_1729026 := by exact prefixLift 1729026
  have htrace : WordTrace (prefixWord ++ tailWord_1729026) baseStart_1729026 baseEnd_1729026 := by
    simpa [prefixWord, tailWord_1729026, baseEnd_1729026] using wordTrace_append hprefix tailTrace_1729026
  have hstable : (prefixWord ++ tailWord_1729026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729026).length < 2 ^ (prefixWord ++ tailWord_1729026).sum := by decide
  have hdescent : baseEnd_1729026 < baseStart_1729026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729050 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_1729050 : Nat := 118140960795 + 1729050 * 2 ^ 59
def prefixEnd_1729050 : Nat := 4983230072969 + 3 ^ 40 * 1729050 * 2
def baseEnd_1729050 : Nat := 197296383479236737249611

theorem tailTrace_1729050 : CollatzResearch.WordTrace tailWord_1729050 prefixEnd_1729050 197296383479236737249611 := by
  unfold tailWord_1729050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765908596488655768804151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42042422923969748716811069 15765908596488655768804151)
  ·
    refine ⟨23648862894732983653206227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15765908596488655768804151 23648862894732983653206227)
    ·
      refine ⟨35473294342099475479809341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23648862894732983653206227 35473294342099475479809341)
      ·
        refine ⟨13302485378287303304928503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35473294342099475479809341 13302485378287303304928503)
        ·
          refine ⟨19953728067430954957392755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13302485378287303304928503 19953728067430954957392755)
          ·
            refine ⟨29930592101146432436089133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19953728067430954957392755 29930592101146432436089133)
            ·
              refine ⟨11223972037929912163533425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29930592101146432436089133 11223972037929912163533425)
              ·
                refine ⟨8417979028447434122650069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11223972037929912163533425 8417979028447434122650069)
                ·
                  refine ⟨197296383479236737249611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8417979028447434122650069 197296383479236737249611)
                  ·
                    rfl

theorem cell22_1729050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_1729050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729050 prefixEnd_1729050 := by exact prefixLift 1729050
  have htrace : WordTrace (prefixWord ++ tailWord_1729050) baseStart_1729050 baseEnd_1729050 := by
    simpa [prefixWord, tailWord_1729050, baseEnd_1729050] using wordTrace_append hprefix tailTrace_1729050
  have hstable : (prefixWord ++ tailWord_1729050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729050).length < 2 ^ (prefixWord ++ tailWord_1729050).sum := by decide
  have hdescent : baseEnd_1729050 < baseStart_1729050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729084 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 5]
def baseStart_1729084 : Nat := 118140960795 + 1729084 * 2 ^ 59
def prefixEnd_1729084 : Nat := 4983230072969 + 3 ^ 40 * 1729084 * 2
def baseEnd_1729084 : Nat := 197300263110848485466243

theorem tailTrace_1729084 : CollatzResearch.WordTrace tailWord_1729084 prefixEnd_1729084 197300263110848485466243 := by
  unfold tailWord_1729084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31532437233915723440977153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42043249645220964587969537 31532437233915723440977153)
  ·
    refine ⟨23649327925436792580732865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31532437233915723440977153 23649327925436792580732865)
    ·
      refine ⟨17736995944077594435549649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23649327925436792580732865 17736995944077594435549649)
      ·
        refine ⟨13302746958058195826662237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17736995944077594435549649 13302746958058195826662237)
        ·
          refine ⟨4988530109271823434998339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13302746958058195826662237 4988530109271823434998339)
          ·
            refine ⟨7482795163907735152497509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988530109271823434998339 7482795163907735152497509)
            ·
              refine ⟨1403024093232700341093283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7482795163907735152497509 1403024093232700341093283)
              ·
                refine ⟨2104536139849050511639925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403024093232700341093283 2104536139849050511639925)
                ·
                  refine ⟨197300263110848485466243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2104536139849050511639925 197300263110848485466243)
                  ·
                    rfl

theorem cell22_1729084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_1729084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729084 prefixEnd_1729084 := by exact prefixLift 1729084
  have htrace : WordTrace (prefixWord ++ tailWord_1729084) baseStart_1729084 baseEnd_1729084 := by
    simpa [prefixWord, tailWord_1729084, baseEnd_1729084] using wordTrace_append hprefix tailTrace_1729084
  have hstable : (prefixWord ++ tailWord_1729084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729084).length < 2 ^ (prefixWord ++ tailWord_1729084).sum := by decide
  have hdescent : baseEnd_1729084 < baseStart_1729084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729122 : List Nat := [3, 3, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1729122 : Nat := 118140960795 + 1729122 * 2 ^ 59
def prefixEnd_1729122 : Nat := 4983230072969 + 3 ^ 40 * 1729122 * 2
def baseEnd_1729122 : Nat := 591913797509126023948613

theorem tailTrace_1729122 : CollatzResearch.WordTrace tailWord_1729122 prefixEnd_1729122 591913797509126023948613 := by
  unfold tailWord_1729122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15766565110423444842959405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42044173627795852914558413 15766565110423444842959405)
  ·
    refine ⟨5912461916408791816109777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15766565110423444842959405 5912461916408791816109777)
    ·
      refine ⟨4434346437306593862082333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5912461916408791816109777 4434346437306593862082333)
      ·
        refine ⟨1662879913989972698280875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4434346437306593862082333 1662879913989972698280875)
        ·
          refine ⟨2494319870984959047421313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662879913989972698280875 2494319870984959047421313)
          ·
            refine ⟨1870739903238719285565985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494319870984959047421313 1870739903238719285565985)
            ·
              refine ⟨1403054927429039464174489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870739903238719285565985 1403054927429039464174489)
              ·
                refine ⟨1052291195571779598130867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403054927429039464174489 1052291195571779598130867)
                ·
                  refine ⟨1578436793357669397196301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052291195571779598130867 1578436793357669397196301)
                  ·
                    refine ⟨591913797509126023948613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1578436793357669397196301 591913797509126023948613)
                    ·
                      rfl

theorem cell22_1729122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1729122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729122 prefixEnd_1729122 := by exact prefixLift 1729122
  have htrace : WordTrace (prefixWord ++ tailWord_1729122) baseStart_1729122 baseEnd_1729122 := by
    simpa [prefixWord, tailWord_1729122, baseEnd_1729122] using wordTrace_append hprefix tailTrace_1729122
  have hstable : (prefixWord ++ tailWord_1729122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729122).length < 2 ^ (prefixWord ++ tailWord_1729122).sum := by decide
  have hdescent : baseEnd_1729122 < baseStart_1729122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729266 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1729266 : Nat := 118140960795 + 1729266 * 2 ^ 59
def prefixEnd_1729266 : Nat := 4983230072969 + 3 ^ 40 * 1729266 * 2
def baseEnd_1729266 : Nat := 591963091651957648348171

theorem tailTrace_1729266 : CollatzResearch.WordTrace tailWord_1729266 prefixEnd_1729266 591963091651957648348171 := by
  unfold tailWord_1729266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767878138293022991269913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42047675035448061310053101 15767878138293022991269913)
  ·
    refine ⟨11825908603719767243452435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15767878138293022991269913 11825908603719767243452435)
    ·
      refine ⟨17738862905579650865178653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11825908603719767243452435 17738862905579650865178653)
      ·
        refine ⟨6652073589592369074441995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17738862905579650865178653 6652073589592369074441995)
        ·
          refine ⟨9978110384388553611662993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6652073589592369074441995 9978110384388553611662993)
          ·
            refine ⟨7483582788291415208747245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9978110384388553611662993 7483582788291415208747245)
            ·
              refine ⟨2806343545609280703280217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7483582788291415208747245 2806343545609280703280217)
              ·
                refine ⟨2104757659206960527460163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806343545609280703280217 2104757659206960527460163)
                ·
                  refine ⟨3157136488810440791190245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104757659206960527460163 3157136488810440791190245)
                  ·
                    refine ⟨591963091651957648348171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3157136488810440791190245 591963091651957648348171)
                    ·
                      rfl

theorem cell22_1729266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1729266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729266 prefixEnd_1729266 := by exact prefixLift 1729266
  have htrace : WordTrace (prefixWord ++ tailWord_1729266) baseStart_1729266 baseEnd_1729266 := by
    simpa [prefixWord, tailWord_1729266, baseEnd_1729266] using wordTrace_append hprefix tailTrace_1729266
  have hstable : (prefixWord ++ tailWord_1729266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729266).length < 2 ^ (prefixWord ++ tailWord_1729266).sum := by decide
  have hdescent : baseEnd_1729266 < baseStart_1729266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729354 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_1729354 : Nat := 118140960795 + 1729354 * 2 ^ 59
def prefixEnd_1729354 : Nat := 4983230072969 + 3 ^ 40 * 1729354 * 2
def baseEnd_1729354 : Nat := 197331071950118250715967

theorem tailTrace_1729354 : CollatzResearch.WordTrace tailWord_1729354 prefixEnd_1729354 197331071950118250715967 := by
  unfold tailWord_1729354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15768680544213320748570779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42049814784568855329522077 15768680544213320748570779)
  ·
    refine ⟨23653020816319981122856169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15768680544213320748570779 23653020816319981122856169)
    ·
      refine ⟨17739765612239985842142127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23653020816319981122856169 17739765612239985842142127)
      ·
        refine ⟨26609648418359978763213191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17739765612239985842142127 26609648418359978763213191)
        ·
          refine ⟨39914472627539968144819787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26609648418359978763213191 39914472627539968144819787)
          ·
            refine ⟨59871708941309952217229681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39914472627539968144819787 59871708941309952217229681)
            ·
              refine ⟨44903781705982464162922261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59871708941309952217229681 44903781705982464162922261)
              ·
                refine ⟨2104864767467928007636981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44903781705982464162922261 2104864767467928007636981)
                ·
                  refine ⟨197331071950118250715967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2104864767467928007636981 197331071950118250715967)
                  ·
                    rfl

theorem cell22_1729354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_1729354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729354 prefixEnd_1729354 := by exact prefixLift 1729354
  have htrace : WordTrace (prefixWord ++ tailWord_1729354) baseStart_1729354 baseEnd_1729354 := by
    simpa [prefixWord, tailWord_1729354, baseEnd_1729354] using wordTrace_append hprefix tailTrace_1729354
  have hstable : (prefixWord ++ tailWord_1729354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729354).length < 2 ^ (prefixWord ++ tailWord_1729354).sum := by decide
  have hdescent : baseEnd_1729354 < baseStart_1729354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729369 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_1729369 : Nat := 118140960795 + 1729369 * 2 ^ 59
def prefixEnd_1729369 : Nat := 4983230072969 + 3 ^ 40 * 1729369 * 2
def baseEnd_1729369 : Nat := 591998350656899713022855

theorem tailTrace_1729369 : CollatzResearch.WordTrace tailWord_1729369 prefixEnd_1729369 591998350656899713022855 := by
  unfold tailWord_1729369
  simp only [CollatzResearch.WordTrace]
  refine ⟨63075269271798940556079161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42050179514532627037386107 63075269271798940556079161)
  ·
    refine ⟨47306451953849205417059371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63075269271798940556079161 47306451953849205417059371)
    ·
      refine ⟨70959677930773808125589057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47306451953849205417059371 70959677930773808125589057)
      ·
        refine ⟨53219758448080356094191793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70959677930773808125589057 53219758448080356094191793)
        ·
          refine ⟨39914818836060267070643845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53219758448080356094191793 39914818836060267070643845)
          ·
            refine ⟨7484028531761300075745721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39914818836060267070643845 7484028531761300075745721)
            ·
              refine ⟨5613021398820975056809291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7484028531761300075745721 5613021398820975056809291)
              ·
                refine ⟨8419532098231462585213937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613021398820975056809291 8419532098231462585213937)
                ·
                  refine ⟨6314649073673596938910453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8419532098231462585213937 6314649073673596938910453)
                  ·
                    refine ⟨591998350656899713022855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6314649073673596938910453 591998350656899713022855)
                    ·
                      rfl

theorem cell22_1729369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_1729369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729369 prefixEnd_1729369 := by exact prefixLift 1729369
  have htrace : WordTrace (prefixWord ++ tailWord_1729369) baseStart_1729369 baseEnd_1729369 := by
    simpa [prefixWord, tailWord_1729369, baseEnd_1729369] using wordTrace_append hprefix tailTrace_1729369
  have hstable : (prefixWord ++ tailWord_1729369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729369).length < 2 ^ (prefixWord ++ tailWord_1729369).sum := by decide
  have hdescent : baseEnd_1729369 < baseStart_1729369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729401 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_1729401 : Nat := 118140960795 + 1729401 * 2 ^ 59
def prefixEnd_1729401 : Nat := 4983230072969 + 3 ^ 40 * 1729401 * 2
def baseEnd_1729401 : Nat := 592009304910862296222757

theorem tailTrace_1729401 : CollatzResearch.WordTrace tailWord_1729401 prefixEnd_1729401 592009304910862296222757 := by
  unfold tailWord_1729401
  simp only [CollatzResearch.WordTrace]
  refine ⟨63076436407683010021244057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42050957605122006680829371 63076436407683010021244057)
  ·
    refine ⟨47307327305762257515933043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63076436407683010021244057 47307327305762257515933043)
    ·
      refine ⟨70960990958643386273899565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47307327305762257515933043 70960990958643386273899565)
      ·
        refine ⟨26610371609491269852712337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70960990958643386273899565 26610371609491269852712337)
        ·
          refine ⟨19957778707118452389534253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26610371609491269852712337 19957778707118452389534253)
          ·
            refine ⟨7484167015169419646075345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19957778707118452389534253 7484167015169419646075345)
            ·
              refine ⟨5613125261377064734556509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7484167015169419646075345 5613125261377064734556509)
              ·
                refine ⟨2104921973016399275458691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613125261377064734556509 2104921973016399275458691)
                ·
                  refine ⟨3157382959524598913188037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104921973016399275458691 3157382959524598913188037)
                  ·
                    refine ⟨592009304910862296222757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3157382959524598913188037 592009304910862296222757)
                    ·
                      rfl

theorem cell22_1729401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_1729401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729401 prefixEnd_1729401 := by exact prefixLift 1729401
  have htrace : WordTrace (prefixWord ++ tailWord_1729401) baseStart_1729401 baseEnd_1729401 := by
    simpa [prefixWord, tailWord_1729401, baseEnd_1729401] using wordTrace_append hprefix tailTrace_1729401
  have hstable : (prefixWord ++ tailWord_1729401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729401).length < 2 ^ (prefixWord ++ tailWord_1729401).sum := by decide
  have hdescent : baseEnd_1729401 < baseStart_1729401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729416 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 6]
def baseStart_1729416 : Nat := 118140960795 + 1729416 * 2 ^ 59
def prefixEnd_1729416 : Nat := 4983230072969 + 3 ^ 40 * 1729416 * 2
def baseEnd_1729416 : Nat := 197338146572469085699237

theorem tailTrace_1729416 : CollatzResearch.WordTrace tailWord_1729416 prefixEnd_1729416 197338146572469085699237 := by
  unfold tailWord_1729416
  simp only [CollatzResearch.WordTrace]
  refine ⟨31538491751314333791520051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42051322335085778388693401 31538491751314333791520051)
  ·
    refine ⟨47307737626971500687280077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31538491751314333791520051 47307737626971500687280077)
    ·
      refine ⟨17740401610114312757730029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47307737626971500687280077 17740401610114312757730029)
      ·
        refine ⟨6652650603792867284148761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17740401610114312757730029 6652650603792867284148761)
        ·
          refine ⟨4989487952844650463111571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6652650603792867284148761 4989487952844650463111571)
          ·
            refine ⟨7484231929266975694667357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989487952844650463111571 7484231929266975694667357)
            ·
              refine ⟨2806586973475115885500259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7484231929266975694667357 2806586973475115885500259)
              ·
                refine ⟨4209880460212673828250389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806586973475115885500259 4209880460212673828250389)
                ·
                  refine ⟨197338146572469085699237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4209880460212673828250389 197338146572469085699237)
                  ·
                    rfl

theorem cell22_1729416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_1729416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729416 prefixEnd_1729416 := by exact prefixLift 1729416
  have htrace : WordTrace (prefixWord ++ tailWord_1729416) baseStart_1729416 baseEnd_1729416 := by
    simpa [prefixWord, tailWord_1729416, baseEnd_1729416] using wordTrace_append hprefix tailTrace_1729416
  have hstable : (prefixWord ++ tailWord_1729416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729416).length < 2 ^ (prefixWord ++ tailWord_1729416).sum := by decide
  have hdescent : baseEnd_1729416 < baseStart_1729416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729444 : List Nat := [2, 3, 1, 2, 1, 2, 1, 10]
def baseStart_1729444 : Nat := 118140960795 + 1729444 * 2 ^ 59
def prefixEnd_1729444 : Nat := 4983230072969 + 3 ^ 40 * 1729444 * 2
def baseEnd_1729444 : Nat := 65780447187736057488625

theorem tailTrace_1729444 : CollatzResearch.WordTrace tailWord_1729444 prefixEnd_1729444 65780447187736057488625 := by
  unfold tailWord_1729444
  simp only [CollatzResearch.WordTrace]
  refine ⟨31539002373263614182529693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42052003164351485576706257 31539002373263614182529693)
  ·
    refine ⟨11827125889973855318448635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31539002373263614182529693 11827125889973855318448635)
    ·
      refine ⟨17740688834960782977672953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827125889973855318448635 17740688834960782977672953)
      ·
        refine ⟨13305516626220587233254715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17740688834960782977672953 13305516626220587233254715)
        ·
          refine ⟨19958274939330880849882073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13305516626220587233254715 19958274939330880849882073)
          ·
            refine ⟨14968706204498160637411555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19958274939330880849882073 14968706204498160637411555)
            ·
              refine ⟨22453059306747240956117333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14968706204498160637411555 22453059306747240956117333)
              ·
                refine ⟨65780447187736057488625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22453059306747240956117333 65780447187736057488625)
                ·
                  rfl

theorem cell22_1729444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 10].length) (baseStart_1729444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729444 prefixEnd_1729444 := by exact prefixLift 1729444
  have htrace : WordTrace (prefixWord ++ tailWord_1729444) baseStart_1729444 baseEnd_1729444 := by
    simpa [prefixWord, tailWord_1729444, baseEnd_1729444] using wordTrace_append hprefix tailTrace_1729444
  have hstable : (prefixWord ++ tailWord_1729444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729444).length < 2 ^ (prefixWord ++ tailWord_1729444).sum := by decide
  have hdescent : baseEnd_1729444 < baseStart_1729444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729521 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1729521 : Nat := 118140960795 + 1729521 * 2 ^ 59
def prefixEnd_1729521 : Nat := 4983230072969 + 3 ^ 40 * 1729521 * 2
def baseEnd_1729521 : Nat := 592050383363221983222389

theorem tailTrace_1729521 : CollatzResearch.WordTrace tailWord_1729521 prefixEnd_1729521 592050383363221983222389 := by
  unfold tailWord_1729521
  simp only [CollatzResearch.WordTrace]
  refine ⟨63080813167248270515612417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42053875444832180343741611 63080813167248270515612417)
  ·
    refine ⟨47310609875436202886709313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63080813167248270515612417 47310609875436202886709313)
    ·
      refine ⟨35482957406577152165031985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47310609875436202886709313 35482957406577152165031985)
      ·
        refine ⟨26612218054932864123773989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35482957406577152165031985 26612218054932864123773989)
        ·
          refine ⟨4989790885299912023207623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26612218054932864123773989 4989790885299912023207623)
          ·
            refine ⟨7484686327949868034811435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989790885299912023207623 7484686327949868034811435)
            ·
              refine ⟨11227029491924802052217153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484686327949868034811435 11227029491924802052217153)
              ·
                refine ⟨8420272118943601539162865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11227029491924802052217153 8420272118943601539162865)
                ·
                  refine ⟨6315204089207701154372149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8420272118943601539162865 6315204089207701154372149)
                  ·
                    refine ⟨592050383363221983222389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6315204089207701154372149 592050383363221983222389)
                    ·
                      rfl

theorem cell22_1729521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1729521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729521 prefixEnd_1729521 := by exact prefixLift 1729521
  have htrace : WordTrace (prefixWord ++ tailWord_1729521) baseStart_1729521 baseEnd_1729521 := by
    simpa [prefixWord, tailWord_1729521, baseEnd_1729521] using wordTrace_append hprefix tailTrace_1729521
  have hstable : (prefixWord ++ tailWord_1729521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729521).length < 2 ^ (prefixWord ++ tailWord_1729521).sum := by decide
  have hdescent : baseEnd_1729521 < baseStart_1729521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729585 : List Nat := [1, 2, 2, 3, 1, 2, 5, 2, 4]
def baseStart_1729585 : Nat := 118140960795 + 1729585 * 2 ^ 59
def prefixEnd_1729585 : Nat := 4983230072969 + 3 ^ 40 * 1729585 * 2
def baseEnd_1729585 : Nat := 197357430623715716540731

theorem tailTrace_1729585 : CollatzResearch.WordTrace tailWord_1729585 prefixEnd_1729585 197357430623715716540731 := by
  unfold tailWord_1729585
  simp only [CollatzResearch.WordTrace]
  refine ⟨63083147439016409445942209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42055431626010939630628139 63083147439016409445942209)
  ·
    refine ⟨47312360579262307084456657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63083147439016409445942209 47312360579262307084456657)
    ·
      refine ⟨35484270434446730313342493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47312360579262307084456657 35484270434446730313342493)
      ·
        refine ⟨13306601412917523867503435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35484270434446730313342493 13306601412917523867503435)
        ·
          refine ⟨19959902119376285801255153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306601412917523867503435 19959902119376285801255153)
          ·
            refine ⟨14969926589532214350941365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19959902119376285801255153 14969926589532214350941365)
            ·
              refine ⟨1403430617768645095400753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14969926589532214350941365 1403430617768645095400753)
              ·
                refine ⟨1052572963326483821550565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403430617768645095400753 1052572963326483821550565)
                ·
                  refine ⟨197357430623715716540731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052572963326483821550565 197357430623715716540731)
                  ·
                    rfl

theorem cell22_1729585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_1729585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729585 prefixEnd_1729585 := by exact prefixLift 1729585
  have htrace : WordTrace (prefixWord ++ tailWord_1729585) baseStart_1729585 baseEnd_1729585 := by
    simpa [prefixWord, tailWord_1729585, baseEnd_1729585] using wordTrace_append hprefix tailTrace_1729585
  have hstable : (prefixWord ++ tailWord_1729585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729585).length < 2 ^ (prefixWord ++ tailWord_1729585).sum := by decide
  have hdescent : baseEnd_1729585 < baseStart_1729585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729596 : List Nat := [2, 2, 2, 2, 2, 2, 1, 9]
def baseStart_1729596 : Nat := 118140960795 + 1729596 * 2 ^ 59
def prefixEnd_1729596 : Nat := 4983230072969 + 3 ^ 40 * 1729596 * 2
def baseEnd_1729596 : Nat := 65786228599549643066351

theorem tailTrace_1729596 : CollatzResearch.WordTrace tailWord_1729596 prefixEnd_1729596 65786228599549643066351 := by
  unfold tailWord_1729596
  simp only [CollatzResearch.WordTrace]
  refine ⟨31541774320988279162296321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42055699094651038883061761 31541774320988279162296321)
  ·
    refine ⟨23656330740741209371722241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31541774320988279162296321 23656330740741209371722241)
    ·
      refine ⟨17742248055555907028791681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23656330740741209371722241 17742248055555907028791681)
      ·
        refine ⟨13306686041666930271593761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17742248055555907028791681 13306686041666930271593761)
        ·
          refine ⟨9980014531250197703695321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13306686041666930271593761 9980014531250197703695321)
          ·
            refine ⟨7485010898437648277771491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9980014531250197703695321 7485010898437648277771491)
            ·
              refine ⟨11227516347656472416657237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485010898437648277771491 11227516347656472416657237)
              ·
                refine ⟨65786228599549643066351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11227516347656472416657237 65786228599549643066351)
                ·
                  rfl

theorem cell22_1729596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 9].length) (baseStart_1729596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729596 prefixEnd_1729596 := by exact prefixLift 1729596
  have htrace : WordTrace (prefixWord ++ tailWord_1729596) baseStart_1729596 baseEnd_1729596 := by
    simpa [prefixWord, tailWord_1729596, baseEnd_1729596] using wordTrace_append hprefix tailTrace_1729596
  have hstable : (prefixWord ++ tailWord_1729596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729596).length < 2 ^ (prefixWord ++ tailWord_1729596).sum := by decide
  have hdescent : baseEnd_1729596 < baseStart_1729596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729613 : List Nat := [1, 6, 1, 1, 1, 2, 2, 8]
def baseStart_1729613 : Nat := 118140960795 + 1729613 * 2 ^ 59
def prefixEnd_1729613 : Nat := 4983230072969 + 3 ^ 40 * 1729613 * 2
def baseEnd_1729613 : Nat := 65786875204818267769123

theorem tailTrace_1729613 : CollatzResearch.WordTrace tailWord_1729613 prefixEnd_1729613 65786875204818267769123 := by
  unfold tailWord_1729613
  simp only [CollatzResearch.WordTrace]
  refine ⟨63084168682914970227961493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42056112455276646818640995 63084168682914970227961493)
  ·
    refine ⟨2957070407011639229435695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63084168682914970227961493 2957070407011639229435695)
    ·
      refine ⟨4435605610517458844153543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2957070407011639229435695 4435605610517458844153543)
      ·
        refine ⟨6653408415776188266230315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4435605610517458844153543 6653408415776188266230315)
        ·
          refine ⟨9980112623664282399345473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6653408415776188266230315 9980112623664282399345473)
          ·
            refine ⟨7485084467748211799509105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9980112623664282399345473 7485084467748211799509105)
            ·
              refine ⟨5613813350811158849631829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7485084467748211799509105 5613813350811158849631829)
              ·
                refine ⟨65786875204818267769123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5613813350811158849631829 65786875204818267769123)
                ·
                  rfl

theorem cell22_1729613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 8].length) (baseStart_1729613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729613 prefixEnd_1729613 := by exact prefixLift 1729613
  have htrace : WordTrace (prefixWord ++ tailWord_1729613) baseStart_1729613 baseEnd_1729613 := by
    simpa [prefixWord, tailWord_1729613, baseEnd_1729613] using wordTrace_append hprefix tailTrace_1729613
  have hstable : (prefixWord ++ tailWord_1729613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729613).length < 2 ^ (prefixWord ++ tailWord_1729613).sum := by decide
  have hdescent : baseEnd_1729613 < baseStart_1729613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729630 : List Nat := [4, 4, 1, 1, 1, 11]
def baseStart_1729630 : Nat := 118140960795 + 1729630 * 2 ^ 59
def prefixEnd_1729630 : Nat := 4983230072969 + 3 ^ 40 * 1729630 * 2
def baseEnd_1729630 : Nat := 7309724645565210274655

theorem tailTrace_1729630 : CollatzResearch.WordTrace tailWord_1729630 prefixEnd_1729630 7309724645565210274655 := by
  unfold tailWord_1729630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885598590481672766416293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42056525815902254754220229 7885598590481672766416293)
  ·
    refine ⟨1478549735715313643703055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7885598590481672766416293 1478549735715313643703055)
    ·
      refine ⟨2217824603572970465554583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478549735715313643703055 2217824603572970465554583)
      ·
        refine ⟨3326736905359455698331875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217824603572970465554583 3326736905359455698331875)
        ·
          refine ⟨4990105358039183547497813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326736905359455698331875 4990105358039183547497813)
          ·
            refine ⟨7309724645565210274655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4990105358039183547497813 7309724645565210274655)
            ·
              rfl

theorem cell22_1729630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 11].length) (baseStart_1729630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729630 prefixEnd_1729630 := by exact prefixLift 1729630
  have htrace : WordTrace (prefixWord ++ tailWord_1729630) baseStart_1729630 baseEnd_1729630 := by
    simpa [prefixWord, tailWord_1729630, baseEnd_1729630] using wordTrace_append hprefix tailTrace_1729630
  have hstable : (prefixWord ++ tailWord_1729630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729630).length < 2 ^ (prefixWord ++ tailWord_1729630).sum := by decide
  have hdescent : baseEnd_1729630 < baseStart_1729630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729656 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_1729656 : Nat := 118140960795 + 1729656 * 2 ^ 59
def prefixEnd_1729656 : Nat := 4983230072969 + 3 ^ 40 * 1729656 * 2
def baseEnd_1729656 : Nat := 592096596622126631096975

theorem tailTrace_1729656 : CollatzResearch.WordTrace tailWord_1729656 prefixEnd_1729656 592096596622126631096975 := by
  unfold tailWord_1729656
  simp only [CollatzResearch.WordTrace]
  refine ⟨31542868510879594285888411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42057158014506125714517881 31542868510879594285888411)
  ·
    refine ⟨47314302766319391428832617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31542868510879594285888411 47314302766319391428832617)
    ·
      refine ⟨35485727074739543571624463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47314302766319391428832617 35485727074739543571624463)
      ·
        refine ⟨53228590612109315357436695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35485727074739543571624463 53228590612109315357436695)
        ·
          refine ⟨79842885918163973036155043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53228590612109315357436695 79842885918163973036155043)
          ·
            refine ⟨119764328877245959554232565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79842885918163973036155043 119764328877245959554232565)
            ·
              refine ⟨11227905832241808708209303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119764328877245959554232565 11227905832241808708209303)
              ·
                refine ⟨16841858748362713062313955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11227905832241808708209303 16841858748362713062313955)
                ·
                  refine ⟨25262788122544069593470933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16841858748362713062313955 25262788122544069593470933)
                  ·
                    refine ⟨592096596622126631096975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25262788122544069593470933 592096596622126631096975)
                    ·
                      rfl

theorem cell22_1729656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_1729656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729656 prefixEnd_1729656 := by exact prefixLift 1729656
  have htrace : WordTrace (prefixWord ++ tailWord_1729656) baseStart_1729656 baseEnd_1729656 := by
    simpa [prefixWord, tailWord_1729656, baseEnd_1729656] using wordTrace_append hprefix tailTrace_1729656
  have hstable : (prefixWord ++ tailWord_1729656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729656).length < 2 ^ (prefixWord ++ tailWord_1729656).sum := by decide
  have hdescent : baseEnd_1729656 < baseStart_1729656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729730 : List Nat := [3, 5, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1729730 : Nat := 118140960795 + 1729730 * 2 ^ 59
def prefixEnd_1729730 : Nat := 4983230072969 + 3 ^ 40 * 1729730 * 2
def baseEnd_1729730 : Nat := 592121928334415104746749

theorem tailTrace_1729730 : CollatzResearch.WordTrace tailWord_1729730 prefixEnd_1729730 592121928334415104746749 := by
  unfold tailWord_1729730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15772109005872774802492661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42058957348994066139980429 15772109005872774802492661)
  ·
    refine ⟨1478635219300572637733687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15772109005872774802492661 1478635219300572637733687)
    ·
      refine ⟨2217952828950858956600531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478635219300572637733687 2217952828950858956600531)
      ·
        refine ⟨3326929243426288434900797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217952828950858956600531 3326929243426288434900797)
        ·
          refine ⟨1247598466284858163087799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3326929243426288434900797 1247598466284858163087799)
          ·
            refine ⟨1871397699427287244631699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247598466284858163087799 1871397699427287244631699)
            ·
              refine ⟨2807096549140930866947549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871397699427287244631699 2807096549140930866947549)
              ·
                refine ⟨1052661205927849075105331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2807096549140930866947549 1052661205927849075105331)
                ·
                  refine ⟨1578991808891773612657997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052661205927849075105331 1578991808891773612657997)
                  ·
                    refine ⟨592121928334415104746749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1578991808891773612657997 592121928334415104746749)
                    ·
                      rfl

theorem cell22_1729730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1729730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729730 prefixEnd_1729730 := by exact prefixLift 1729730
  have htrace : WordTrace (prefixWord ++ tailWord_1729730) baseStart_1729730 baseEnd_1729730 := by
    simpa [prefixWord, tailWord_1729730, baseEnd_1729730] using wordTrace_append hprefix tailTrace_1729730
  have hstable : (prefixWord ++ tailWord_1729730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729730).length < 2 ^ (prefixWord ++ tailWord_1729730).sum := by decide
  have hdescent : baseEnd_1729730 < baseStart_1729730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729733 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_1729733 : Nat := 118140960795 + 1729733 * 2 ^ 59
def prefixEnd_1729733 : Nat := 4983230072969 + 3 ^ 40 * 1729733 * 2
def baseEnd_1729733 : Nat := 592122955295724096921739

theorem tailTrace_1729733 : CollatzResearch.WordTrace tailWord_1729733 prefixEnd_1729733 592122955295724096921739 := by
  unfold tailWord_1729733
  simp only [CollatzResearch.WordTrace]
  refine ⟨63088545442480230722329853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42059030294986820481553235 63088545442480230722329853)
  ·
    refine ⟨23658204540930086520873695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63088545442480230722329853 23658204540930086520873695)
    ·
      refine ⟨35487306811395129781310543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23658204540930086520873695 35487306811395129781310543)
      ·
        refine ⟨53230960217092694671965815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35487306811395129781310543 53230960217092694671965815)
        ·
          refine ⟨79846440325639042007948723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53230960217092694671965815 79846440325639042007948723)
          ·
            refine ⟨119769660488458563011923085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79846440325639042007948723 119769660488458563011923085)
            ·
              refine ⟨44913622683171961129471157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119769660488458563011923085 44913622683171961129471157)
              ·
                refine ⟨4210652126547371355887921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44913622683171961129471157 4210652126547371355887921)
                ·
                  refine ⟨3157989094910528516915941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210652126547371355887921 3157989094910528516915941)
                  ·
                    refine ⟨592122955295724096921739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3157989094910528516915941 592122955295724096921739)
                    ·
                      rfl

theorem cell22_1729733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_1729733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729733 prefixEnd_1729733 := by exact prefixLift 1729733
  have htrace : WordTrace (prefixWord ++ tailWord_1729733) baseStart_1729733 baseEnd_1729733 := by
    simpa [prefixWord, tailWord_1729733, baseEnd_1729733] using wordTrace_append hprefix tailTrace_1729733
  have hstable : (prefixWord ++ tailWord_1729733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729733).length < 2 ^ (prefixWord ++ tailWord_1729733).sum := by decide
  have hdescent : baseEnd_1729733 < baseStart_1729733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729765 : List Nat := [1, 3, 1, 4, 3, 1, 2, 7]
def baseStart_1729765 : Nat := 118140960795 + 1729765 * 2 ^ 59
def prefixEnd_1729765 : Nat := 4983230072969 + 3 ^ 40 * 1729765 * 2
def baseEnd_1729765 : Nat := 65792656616631853346849

theorem tailTrace_1729765 : CollatzResearch.WordTrace tailWord_1729765 prefixEnd_1729765 65792656616631853346849 := by
  unfold tailWord_1729765
  simp only [CollatzResearch.WordTrace]
  refine ⟨63089712578364300187494749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42059808385576200124996499 63089712578364300187494749)
  ·
    refine ⟨23658642216886612570310531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63089712578364300187494749 23658642216886612570310531)
    ·
      refine ⟨35487963325329918855465797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23658642216886612570310531 35487963325329918855465797)
      ·
        refine ⟨6653993123499359785399837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35487963325329918855465797 6653993123499359785399837)
        ·
          refine ⟨2495247421312259919524939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6653993123499359785399837 2495247421312259919524939)
          ·
            refine ⟨3742871131968389879287409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495247421312259919524939 3742871131968389879287409)
            ·
              refine ⟨2807153348976292409465557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742871131968389879287409 2807153348976292409465557)
              ·
                refine ⟨65792656616631853346849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2807153348976292409465557 65792656616631853346849)
                ·
                  rfl

theorem cell22_1729765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 7].length) (baseStart_1729765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729765 prefixEnd_1729765 := by exact prefixLift 1729765
  have htrace : WordTrace (prefixWord ++ tailWord_1729765) baseStart_1729765 baseEnd_1729765 := by
    simpa [prefixWord, tailWord_1729765, baseEnd_1729765] using wordTrace_append hprefix tailTrace_1729765
  have hstable : (prefixWord ++ tailWord_1729765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729765).length < 2 ^ (prefixWord ++ tailWord_1729765).sum := by decide
  have hdescent : baseEnd_1729765 < baseStart_1729765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729797 : List Nat := [1, 3, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_1729797 : Nat := 118140960795 + 1729797 * 2 ^ 59
def prefixEnd_1729797 : Nat := 4983230072969 + 3 ^ 40 * 1729797 * 2
def baseEnd_1729797 : Nat := 592144863803649263321543

theorem tailTrace_1729797 : CollatzResearch.WordTrace tailWord_1729797 prefixEnd_1729797 592144863803649263321543 := by
  unfold tailWord_1729797
  simp only [CollatzResearch.WordTrace]
  refine ⟨63090879714248369652659645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42060586476165579768439763 63090879714248369652659645)
  ·
    refine ⟨23659079892843138619747367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63090879714248369652659645 23659079892843138619747367)
    ·
      refine ⟨35488619839264707929621051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23659079892843138619747367 35488619839264707929621051)
      ·
        refine ⟨53232929758897061894431577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35488619839264707929621051 53232929758897061894431577)
        ·
          refine ⟨39924697319172796420823683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53232929758897061894431577 39924697319172796420823683)
          ·
            refine ⟨59887045978759194631235525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39924697319172796420823683 59887045978759194631235525)
            ·
              refine ⟨11228821121017348993356661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59887045978759194631235525 11228821121017348993356661)
              ·
                refine ⟨1052701980095376468127187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11228821121017348993356661 1052701980095376468127187)
                ·
                  refine ⟨1579052970143064702190781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052701980095376468127187 1579052970143064702190781)
                  ·
                    refine ⟨592144863803649263321543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1579052970143064702190781 592144863803649263321543)
                    ·
                      rfl

theorem cell22_1729797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_1729797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729797 prefixEnd_1729797 := by exact prefixLift 1729797
  have htrace : WordTrace (prefixWord ++ tailWord_1729797) baseStart_1729797 baseEnd_1729797 := by
    simpa [prefixWord, tailWord_1729797, baseEnd_1729797] using wordTrace_append hprefix tailTrace_1729797
  have hstable : (prefixWord ++ tailWord_1729797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729797).length < 2 ^ (prefixWord ++ tailWord_1729797).sum := by decide
  have hdescent : baseEnd_1729797 < baseStart_1729797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729840 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_1729840 : Nat := 118140960795 + 1729840 * 2 ^ 59
def prefixEnd_1729840 : Nat := 4983230072969 + 3 ^ 40 * 1729840 * 2
def baseEnd_1729840 : Nat := 592159583582411484496411

theorem tailTrace_1729840 : CollatzResearch.WordTrace tailWord_1729840 prefixEnd_1729840 592159583582411484496411 := by
  unfold tailWord_1729840
  simp only [CollatzResearch.WordTrace]
  refine ⟨31546224026546293998237487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42061632035395058664316649 31546224026546293998237487)
  ·
    refine ⟨47319336039819440997356231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31546224026546293998237487 47319336039819440997356231)
    ·
      refine ⟨70979004059729161496034347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47319336039819440997356231 70979004059729161496034347)
      ·
        refine ⟨106468506089593742244051521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70979004059729161496034347 106468506089593742244051521)
        ·
          refine ⟨79851379567195306683038641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106468506089593742244051521 79851379567195306683038641)
          ·
            refine ⟨59888534675396480012278981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79851379567195306683038641 59888534675396480012278981)
            ·
              refine ⟨11229100251636840002302309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59888534675396480012278981 11229100251636840002302309)
              ·
                refine ⟨2105456297181907500431683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11229100251636840002302309 2105456297181907500431683)
                ·
                  refine ⟨3158184445772861250647525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105456297181907500431683 3158184445772861250647525)
                  ·
                    refine ⟨592159583582411484496411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3158184445772861250647525 592159583582411484496411)
                    ·
                      rfl

theorem cell22_1729840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_1729840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729840 prefixEnd_1729840 := by exact prefixLift 1729840
  have htrace : WordTrace (prefixWord ++ tailWord_1729840) baseStart_1729840 baseEnd_1729840 := by
    simpa [prefixWord, tailWord_1729840, baseEnd_1729840] using wordTrace_append hprefix tailTrace_1729840
  have hstable : (prefixWord ++ tailWord_1729840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729840).length < 2 ^ (prefixWord ++ tailWord_1729840).sum := by decide
  have hdescent : baseEnd_1729840 < baseStart_1729840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729900 : List Nat := [2, 2, 1, 1, 5, 2, 1, 8]
def baseStart_1729900 : Nat := 118140960795 + 1729900 * 2 ^ 59
def prefixEnd_1729900 : Nat := 4983230072969 + 3 ^ 40 * 1729900 * 2
def baseEnd_1729900 : Nat := 65797791423176814221803

theorem tailTrace_1729900 : CollatzResearch.WordTrace tailWord_1729900 prefixEnd_1729900 65797791423176814221803 := by
  unfold tailWord_1729900
  simp only [CollatzResearch.WordTrace]
  refine ⟨31547318216437609121829577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42063090955250145495772769 31547318216437609121829577)
  ·
    refine ⟨23660488662328206841372183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31547318216437609121829577 23660488662328206841372183)
    ·
      refine ⟨35490732993492310262058275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23660488662328206841372183 35490732993492310262058275)
      ·
        refine ⟨53236099490238465393087413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35490732993492310262058275 53236099490238465393087413)
        ·
          refine ⟨4990884327209856130601945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53236099490238465393087413 4990884327209856130601945)
          ·
            refine ⟨3743163245407392097951459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4990884327209856130601945 3743163245407392097951459)
            ·
              refine ⟨5614744868111088146927189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743163245407392097951459 5614744868111088146927189)
              ·
                refine ⟨65797791423176814221803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5614744868111088146927189 65797791423176814221803)
                ·
                  rfl

theorem cell22_1729900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 8].length) (baseStart_1729900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1729900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1729900 prefixEnd_1729900 := by exact prefixLift 1729900
  have htrace : WordTrace (prefixWord ++ tailWord_1729900) baseStart_1729900 baseEnd_1729900 := by
    simpa [prefixWord, tailWord_1729900, baseEnd_1729900] using wordTrace_append hprefix tailTrace_1729900
  have hstable : (prefixWord ++ tailWord_1729900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729900).length < 2 ^ (prefixWord ++ tailWord_1729900).sum := by decide
  have hdescent : baseEnd_1729900 < baseStart_1729900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730024 : List Nat := [2, 1, 4, 1, 1, 2, 4, 3, 4]
def baseStart_1730024 : Nat := 118140960795 + 1730024 * 2 ^ 59
def prefixEnd_1730024 : Nat := 4983230072969 + 3 ^ 40 * 1730024 * 2
def baseEnd_1730024 : Nat := 197407523514232112631949

theorem tailTrace_1730024 : CollatzResearch.WordTrace tailWord_1730024 prefixEnd_1730024 197407523514232112631949 := by
  unfold tailWord_1730024
  simp only [CollatzResearch.WordTrace]
  refine ⟨31549579542212993710586563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42066106056283991614115417 31549579542212993710586563)
  ·
    refine ⟨47324369313319490565879845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31549579542212993710586563 47324369313319490565879845)
    ·
      refine ⟨8873319246247404481102471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47324369313319490565879845 8873319246247404481102471)
      ·
        refine ⟨13309978869371106721653707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8873319246247404481102471 13309978869371106721653707)
        ·
          refine ⟨19964968304056660082480561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13309978869371106721653707 19964968304056660082480561)
          ·
            refine ⟨14973726228042495061860421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19964968304056660082480561 14973726228042495061860421)
            ·
              refine ⟨2807573667757967824098829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14973726228042495061860421 2807573667757967824098829)
              ·
                refine ⟨1052840125409237934037061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2807573667757967824098829 1052840125409237934037061)
                ·
                  refine ⟨197407523514232112631949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052840125409237934037061 197407523514232112631949)
                  ·
                    rfl

theorem cell22_1730024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_1730024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730024 prefixEnd_1730024 := by exact prefixLift 1730024
  have htrace : WordTrace (prefixWord ++ tailWord_1730024) baseStart_1730024 baseEnd_1730024 := by
    simpa [prefixWord, tailWord_1730024, baseEnd_1730024] using wordTrace_append hprefix tailTrace_1730024
  have hstable : (prefixWord ++ tailWord_1730024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730024).length < 2 ^ (prefixWord ++ tailWord_1730024).sum := by decide
  have hdescent : baseEnd_1730024 < baseStart_1730024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730069 : List Nat := [1, 3, 2, 1, 3, 4, 2, 6]
def baseStart_1730069 : Nat := 118140960795 + 1730069 * 2 ^ 59
def prefixEnd_1730069 : Nat := 4983230072969 + 3 ^ 40 * 1730069 * 2
def baseEnd_1730069 : Nat := 65804219440259024502301

theorem tailTrace_1730069 : CollatzResearch.WordTrace tailWord_1730069 prefixEnd_1730069 65804219440259024502301 := by
  unfold tailWord_1730069
  simp only [CollatzResearch.WordTrace]
  refine ⟨63100800369262960106561261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42067200246175306737707507 63100800369262960106561261)
  ·
    refine ⟨23662800138473610039960473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63100800369262960106561261 23662800138473610039960473)
    ·
      refine ⟨17747100103855207529970355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23662800138473610039960473 17747100103855207529970355)
      ·
        refine ⟨26620650155782811294955533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17747100103855207529970355 26620650155782811294955533)
        ·
          refine ⟨9982743808418554235608325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26620650155782811294955533 9982743808418554235608325)
          ·
            refine ⟨1871764464078478919176561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9982743808418554235608325 1871764464078478919176561)
            ·
              refine ⟨1403823348058859189382421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871764464078478919176561 1403823348058859189382421)
              ·
                refine ⟨65804219440259024502301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1403823348058859189382421 65804219440259024502301)
                ·
                  rfl

theorem cell22_1730069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 6].length) (baseStart_1730069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730069 prefixEnd_1730069 := by exact prefixLift 1730069
  have htrace : WordTrace (prefixWord ++ tailWord_1730069) baseStart_1730069 baseEnd_1730069 := by
    simpa [prefixWord, tailWord_1730069, baseEnd_1730069] using wordTrace_append hprefix tailTrace_1730069
  have hstable : (prefixWord ++ tailWord_1730069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730069).length < 2 ^ (prefixWord ++ tailWord_1730069).sum := by decide
  have hdescent : baseEnd_1730069 < baseStart_1730069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730097 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 5]
def baseStart_1730097 : Nat := 118140960795 + 1730097 * 2 ^ 59
def prefixEnd_1730097 : Nat := 4983230072969 + 3 ^ 40 * 1730097 * 2
def baseEnd_1730097 : Nat := 197415853311516160273541

theorem tailTrace_1730097 : CollatzResearch.WordTrace tailWord_1730097 prefixEnd_1730097 197415853311516160273541 := by
  unfold tailWord_1730097
  simp only [CollatzResearch.WordTrace]
  refine ⟨63101821613161520888580545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42067881075441013925720363 63101821613161520888580545)
  ·
    refine ⟨47326366209871140666435409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63101821613161520888580545 47326366209871140666435409)
    ·
      refine ⟨35494774657403355499826557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47326366209871140666435409 35494774657403355499826557)
      ·
        refine ⟨13310540496526258312434959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35494774657403355499826557 13310540496526258312434959)
        ·
          refine ⟨19965810744789387468652439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13310540496526258312434959 19965810744789387468652439)
          ·
            refine ⟨29948716117184081202978659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19965810744789387468652439 29948716117184081202978659)
            ·
              refine ⟨44923074175776121804467989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29948716117184081202978659 44923074175776121804467989)
              ·
                refine ⟨2105769101989505709584437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44923074175776121804467989 2105769101989505709584437)
                ·
                  refine ⟨197415853311516160273541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2105769101989505709584437 197415853311516160273541)
                  ·
                    rfl

theorem cell22_1730097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_1730097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730097 prefixEnd_1730097 := by exact prefixLift 1730097
  have htrace : WordTrace (prefixWord ++ tailWord_1730097) baseStart_1730097 baseEnd_1730097 := by
    simpa [prefixWord, tailWord_1730097, baseEnd_1730097] using wordTrace_append hprefix tailTrace_1730097
  have hstable : (prefixWord ++ tailWord_1730097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730097).length < 2 ^ (prefixWord ++ tailWord_1730097).sum := by decide
  have hdescent : baseEnd_1730097 < baseStart_1730097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730101 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1730101 : Nat := 118140960795 + 1730101 * 2 ^ 59
def prefixEnd_1730101 : Nat := 4983230072969 + 3 ^ 40 * 1730101 * 2
def baseEnd_1730101 : Nat := 592248929216293803720611

theorem tailTrace_1730101 : CollatzResearch.WordTrace tailWord_1730101 prefixEnd_1730101 592248929216293803720611 := by
  unfold tailWord_1730101
  simp only [CollatzResearch.WordTrace]
  refine ⟨63101967505147029571726157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42067978336764686381150771 63101967505147029571726157)
  ·
    refine ⟨23663237814430136089397309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63101967505147029571726157 23663237814430136089397309)
    ·
      refine ⟨8873714180411301033523991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23663237814430136089397309 8873714180411301033523991)
      ·
        refine ⟨13310571270616951550285987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8873714180411301033523991 13310571270616951550285987)
        ·
          refine ⟨19965856905925427325428981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13310571270616951550285987 19965856905925427325428981)
          ·
            refine ⟨1871799084930508811758967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19965856905925427325428981 1871799084930508811758967)
            ·
              refine ⟨2807698627395763217638451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871799084930508811758967 2807698627395763217638451)
              ·
                refine ⟨4211547941093644826457677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807698627395763217638451 4211547941093644826457677)
                ·
                  refine ⟨1579330477910116809921629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4211547941093644826457677 1579330477910116809921629)
                  ·
                    refine ⟨592248929216293803720611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1579330477910116809921629 592248929216293803720611)
                    ·
                      rfl

theorem cell22_1730101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1730101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730101 prefixEnd_1730101 := by exact prefixLift 1730101
  have htrace : WordTrace (prefixWord ++ tailWord_1730101) baseStart_1730101 baseEnd_1730101 := by
    simpa [prefixWord, tailWord_1730101, baseEnd_1730101] using wordTrace_append hprefix tailTrace_1730101
  have hstable : (prefixWord ++ tailWord_1730101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730101).length < 2 ^ (prefixWord ++ tailWord_1730101).sum := by decide
  have hdescent : baseEnd_1730101 < baseStart_1730101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730172 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1730172 : Nat := 118140960795 + 1730172 * 2 ^ 59
def prefixEnd_1730172 : Nat := 4983230072969 + 3 ^ 40 * 1730172 * 2
def baseEnd_1730172 : Nat := 592273233967273285195393

theorem tailTrace_1730172 : CollatzResearch.WordTrace tailWord_1730172 prefixEnd_1730172 592273233967273285195393 := by
  unfold tailWord_1730172
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552278543944904348780385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42069704725259872465040513 31552278543944904348780385)
  ·
    refine ⟨23664208907958678261585289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31552278543944904348780385 23664208907958678261585289)
    ·
      refine ⟨17748156680969008696188967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23664208907958678261585289 17748156680969008696188967)
      ·
        refine ⟨26622235021453513044283451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17748156680969008696188967 26622235021453513044283451)
        ·
          refine ⟨39933352532180269566425177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26622235021453513044283451 39933352532180269566425177)
          ·
            refine ⟨29950014399135202174818883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39933352532180269566425177 29950014399135202174818883)
            ·
              refine ⟨44925021598702803262228325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29950014399135202174818883 44925021598702803262228325)
              ·
                refine ⟨8423441549756775611667811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44925021598702803262228325 8423441549756775611667811)
                ·
                  refine ⟨12635162324635163417501717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423441549756775611667811 12635162324635163417501717)
                  ·
                    refine ⟨592273233967273285195393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12635162324635163417501717 592273233967273285195393)
                    ·
                      rfl

theorem cell22_1730172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1730172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730172 prefixEnd_1730172 := by exact prefixLift 1730172
  have htrace : WordTrace (prefixWord ++ tailWord_1730172) baseStart_1730172 baseEnd_1730172 := by
    simpa [prefixWord, tailWord_1730172, baseEnd_1730172] using wordTrace_append hprefix tailTrace_1730172
  have hstable : (prefixWord ++ tailWord_1730172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730172).length < 2 ^ (prefixWord ++ tailWord_1730172).sum := by decide
  have hdescent : baseEnd_1730172 < baseStart_1730172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730204 : List Nat := [2, 2, 3, 2, 3, 1, 9]
def baseStart_1730204 : Nat := 118140960795 + 1730204 * 2 ^ 59
def prefixEnd_1730204 : Nat := 4983230072969 + 3 ^ 40 * 1730204 * 2
def baseEnd_1730204 : Nat := 21936451415601328459085

theorem tailTrace_1730204 : CollatzResearch.WordTrace tailWord_1730204 prefixEnd_1730204 21936451415601328459085 := by
  unfold tailWord_1730204
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552862111886939081362833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42070482815849252108483777 31552862111886939081362833)
  ·
    refine ⟨23664646583915204311022125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31552862111886939081362833 23664646583915204311022125)
    ·
      refine ⟨8874242468968201616633297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23664646583915204311022125 8874242468968201616633297)
      ·
        refine ⟨6655681851726151212474973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8874242468968201616633297 6655681851726151212474973)
        ·
          refine ⟨2495880694397306704678115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6655681851726151212474973 2495880694397306704678115)
          ·
            refine ⟨3743821041595960057017173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495880694397306704678115 3743821041595960057017173)
            ·
              refine ⟨21936451415601328459085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3743821041595960057017173 21936451415601328459085)
              ·
                rfl

theorem cell22_1730204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 9].length) (baseStart_1730204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730204 prefixEnd_1730204 := by exact prefixLift 1730204
  have htrace : WordTrace (prefixWord ++ tailWord_1730204) baseStart_1730204 baseEnd_1730204 := by
    simpa [prefixWord, tailWord_1730204, baseEnd_1730204] using wordTrace_append hprefix tailTrace_1730204
  have hstable : (prefixWord ++ tailWord_1730204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730204).length < 2 ^ (prefixWord ++ tailWord_1730204).sum := by decide
  have hdescent : baseEnd_1730204 < baseStart_1730204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730208 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 2, 3]
def baseStart_1730208 : Nat := 118140960795 + 1730208 * 2 ^ 59
def prefixEnd_1730208 : Nat := 4983230072969 + 3 ^ 40 * 1730208 * 2
def baseEnd_1730208 : Nat := 592285557502981191295283

theorem tailTrace_1730208 : CollatzResearch.WordTrace tailWord_1730208 prefixEnd_1730208 592285557502981191295283 := by
  unfold tailWord_1730208
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552935057879693422935639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42070580077172924563914185 31552935057879693422935639)
  ·
    refine ⟨47329402586819540134403459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31552935057879693422935639 47329402586819540134403459)
    ·
      refine ⟨70994103880229310201605189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47329402586819540134403459 70994103880229310201605189)
      ·
        refine ⟨13311394477542995662800973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70994103880229310201605189 13311394477542995662800973)
        ·
          refine ⟨4991772929078623373550365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13311394477542995662800973 4991772929078623373550365)
          ·
            refine ⟨1871914848404483765081387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4991772929078623373550365 1871914848404483765081387)
            ·
              refine ⟨2807872272606725647622081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871914848404483765081387 2807872272606725647622081)
              ·
                refine ⟨2105904204455044235716561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2807872272606725647622081 2105904204455044235716561)
                ·
                  refine ⟨1579428153341283176787421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2105904204455044235716561 1579428153341283176787421)
                  ·
                    refine ⟨592285557502981191295283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1579428153341283176787421 592285557502981191295283)
                    ·
                      rfl

theorem cell22_1730208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_1730208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730208 prefixEnd_1730208 := by exact prefixLift 1730208
  have htrace : WordTrace (prefixWord ++ tailWord_1730208) baseStart_1730208 baseEnd_1730208 := by
    simpa [prefixWord, tailWord_1730208, baseEnd_1730208] using wordTrace_append hprefix tailTrace_1730208
  have hstable : (prefixWord ++ tailWord_1730208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730208).length < 2 ^ (prefixWord ++ tailWord_1730208).sum := by decide
  have hdescent : baseEnd_1730208 < baseStart_1730208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730236 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_1730236 : Nat := 118140960795 + 1730236 * 2 ^ 59
def prefixEnd_1730236 : Nat := 4983230072969 + 3 ^ 40 * 1730236 * 2
def baseEnd_1730236 : Nat := 592295142475198451595197

theorem tailTrace_1730236 : CollatzResearch.WordTrace tailWord_1730236 prefixEnd_1730236 592295142475198451595197 := by
  unfold tailWord_1730236
  simp only [CollatzResearch.WordTrace]
  refine ⟨31553445679828973813945281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42071260906438631751927041 31553445679828973813945281)
  ·
    refine ⟨23665084259871730360458961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31553445679828973813945281 23665084259871730360458961)
    ·
      refine ⟨17748813194903797770344221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23665084259871730360458961 17748813194903797770344221)
      ·
        refine ⟨6655804948088924163879083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17748813194903797770344221 6655804948088924163879083)
        ·
          refine ⟨9983707422133386245818625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655804948088924163879083 9983707422133386245818625)
          ·
            refine ⟨7487780566600039684363969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9983707422133386245818625 7487780566600039684363969)
            ·
              refine ⟨5615835424950029763272977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7487780566600039684363969 5615835424950029763272977)
              ·
                refine ⟨4211876568712522322454733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5615835424950029763272977 4211876568712522322454733)
                ·
                  refine ⟨1579453713267195870920525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4211876568712522322454733 1579453713267195870920525)
                  ·
                    refine ⟨592295142475198451595197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1579453713267195870920525 592295142475198451595197)
                    ·
                      rfl

theorem cell22_1730236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_1730236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730236 prefixEnd_1730236 := by exact prefixLift 1730236
  have htrace : WordTrace (prefixWord ++ tailWord_1730236) baseStart_1730236 baseEnd_1730236 := by
    simpa [prefixWord, tailWord_1730236, baseEnd_1730236] using wordTrace_append hprefix tailTrace_1730236
  have hstable : (prefixWord ++ tailWord_1730236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730236).length < 2 ^ (prefixWord ++ tailWord_1730236).sum := by decide
  have hdescent : baseEnd_1730236 < baseStart_1730236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730328 : List Nat := [2, 1, 2, 3, 1, 1, 6, 2, 4]
def baseStart_1730328 : Nat := 118140960795 + 1730328 * 2 ^ 59
def prefixEnd_1730328 : Nat := 4983230072969 + 3 ^ 40 * 1730328 * 2
def baseEnd_1730328 : Nat := 197442211985113626098305

theorem tailTrace_1730328 : CollatzResearch.WordTrace tailWord_1730328 prefixEnd_1730328 197442211985113626098305 := by
  unfold tailWord_1730328
  simp only [CollatzResearch.WordTrace]
  refine ⟨31555123437662323670119819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42073497916883098226826425 31555123437662323670119819)
  ·
    refine ⟨47332685156493485505179729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31555123437662323670119819 47332685156493485505179729)
    ·
      refine ⟨35499513867370114128884797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47332685156493485505179729 35499513867370114128884797)
      ·
        refine ⟨13312317700263792798331799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35499513867370114128884797 13312317700263792798331799)
        ·
          refine ⟨19968476550395689197497699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13312317700263792798331799 19968476550395689197497699)
          ·
            refine ⟨29952714825593533796246549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19968476550395689197497699 29952714825593533796246549)
            ·
              refine ⟨1404033507449696896699057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29952714825593533796246549 1404033507449696896699057)
              ·
                refine ⟨1053025130587272672524293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404033507449696896699057 1053025130587272672524293)
                ·
                  refine ⟨197442211985113626098305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1053025130587272672524293 197442211985113626098305)
                  ·
                    rfl

theorem cell22_1730328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_1730328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730328 prefixEnd_1730328 := by exact prefixLift 1730328
  have htrace : WordTrace (prefixWord ++ tailWord_1730328) baseStart_1730328 baseEnd_1730328 := by
    simpa [prefixWord, tailWord_1730328, baseEnd_1730328] using wordTrace_append hprefix tailTrace_1730328
  have hstable : (prefixWord ++ tailWord_1730328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730328).length < 2 ^ (prefixWord ++ tailWord_1730328).sum := by decide
  have hdescent : baseEnd_1730328 < baseStart_1730328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730339 : List Nat := [1, 1, 1, 4, 2, 1, 5, 7]
def baseStart_1730339 : Nat := 118140960795 + 1730339 * 2 ^ 59
def prefixEnd_1730339 : Nat := 4983230072969 + 3 ^ 40 * 1730339 * 2
def baseEnd_1730339 : Nat := 65814489053348946252209

theorem tailTrace_1730339 : CollatzResearch.WordTrace tailWord_1730339 prefixEnd_1730339 65814489053348946252209 := by
  unfold tailWord_1730339
  simp only [CollatzResearch.WordTrace]
  refine ⟨63110648078284796218890071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42073765385523197479260047 63110648078284796218890071)
  ·
    refine ⟨94665972117427194328335107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63110648078284796218890071 94665972117427194328335107)
    ·
      refine ⟨141998958176140791492502661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94665972117427194328335107 141998958176140791492502661)
      ·
        refine ⟨26624804658026398404844249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141998958176140791492502661 26624804658026398404844249)
        ·
          refine ⟨19968603493519798803633187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26624804658026398404844249 19968603493519798803633187)
          ·
            refine ⟨29952905240279698205449781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19968603493519798803633187 29952905240279698205449781)
            ·
              refine ⟨2808084866276221706760917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29952905240279698205449781 2808084866276221706760917)
              ·
                refine ⟨65814489053348946252209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2808084866276221706760917 65814489053348946252209)
                ·
                  rfl

theorem cell22_1730339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 7].length) (baseStart_1730339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730339 prefixEnd_1730339 := by exact prefixLift 1730339
  have htrace : WordTrace (prefixWord ++ tailWord_1730339) baseStart_1730339 baseEnd_1730339 := by
    simpa [prefixWord, tailWord_1730339, baseEnd_1730339] using wordTrace_append hprefix tailTrace_1730339
  have hstable : (prefixWord ++ tailWord_1730339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730339).length < 2 ^ (prefixWord ++ tailWord_1730339).sum := by decide
  have hdescent : baseEnd_1730339 < baseStart_1730339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730358 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1730358 : Nat := 118140960795 + 1730358 * 2 ^ 59
def prefixEnd_1730358 : Nat := 4983230072969 + 3 ^ 40 * 1730358 * 2
def baseEnd_1730358 : Nat := 592336905568430800044823

theorem tailTrace_1730358 : CollatzResearch.WordTrace tailWord_1730358 prefixEnd_1730358 592336905568430800044823 := by
  unfold tailWord_1730358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944458816575997653989483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42074227376810641642554485 3944458816575997653989483)
  ·
    refine ⟨5916688224863996480984225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3944458816575997653989483 5916688224863996480984225)
    ·
      refine ⟨4437516168647997360738169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5916688224863996480984225 4437516168647997360738169)
      ·
        refine ⟨3328137126485998020553627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4437516168647997360738169 3328137126485998020553627)
        ·
          refine ⟨4992205689728997030830441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328137126485998020553627 4992205689728997030830441)
          ·
            refine ⟨3744154267296747773122831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4992205689728997030830441 3744154267296747773122831)
            ·
              refine ⟨5616231400945121659684247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744154267296747773122831 5616231400945121659684247)
              ·
                refine ⟨8424347101417682489526371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616231400945121659684247 8424347101417682489526371)
                ·
                  refine ⟨12636520652126523734289557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8424347101417682489526371 12636520652126523734289557)
                  ·
                    refine ⟨592336905568430800044823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12636520652126523734289557 592336905568430800044823)
                    ·
                      rfl

theorem cell22_1730358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1730358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730358 prefixEnd_1730358 := by exact prefixLift 1730358
  have htrace : WordTrace (prefixWord ++ tailWord_1730358) baseStart_1730358 baseEnd_1730358 := by
    simpa [prefixWord, tailWord_1730358, baseEnd_1730358] using wordTrace_append hprefix tailTrace_1730358
  have hstable : (prefixWord ++ tailWord_1730358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730358).length < 2 ^ (prefixWord ++ tailWord_1730358).sum := by decide
  have hdescent : baseEnd_1730358 < baseStart_1730358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730388 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1730388 : Nat := 118140960795 + 1730388 * 2 ^ 59
def prefixEnd_1730388 : Nat := 4983230072969 + 3 ^ 40 * 1730388 * 2
def baseEnd_1730388 : Nat := 592347175181520721794731

theorem tailTrace_1730388 : CollatzResearch.WordTrace tailWord_1730388 prefixEnd_1730388 592347175181520721794731 := by
  unfold tailWord_1730388
  simp only [CollatzResearch.WordTrace]
  refine ⟨31556217627553638793711909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42074956836738185058282545 31556217627553638793711909)
  ·
    refine ⟨5916790805166307273820983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31556217627553638793711909 5916790805166307273820983)
    ·
      refine ⟨8875186207749460910731475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5916790805166307273820983 8875186207749460910731475)
      ·
        refine ⟨13312779311624191366097213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8875186207749460910731475 13312779311624191366097213)
        ·
          refine ⟨4992292241859071762286455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13312779311624191366097213 4992292241859071762286455)
          ·
            refine ⟨7488438362788607643429683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992292241859071762286455 7488438362788607643429683)
            ·
              refine ⟨11232657544182911465144525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488438362788607643429683 11232657544182911465144525)
              ·
                refine ⟨4212246579068591799429197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11232657544182911465144525 4212246579068591799429197)
                ·
                  refine ⟨1579592467150721924785949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4212246579068591799429197 1579592467150721924785949)
                  ·
                    refine ⟨592347175181520721794731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1579592467150721924785949 592347175181520721794731)
                    ·
                      rfl

theorem cell22_1730388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1730388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730388 prefixEnd_1730388 := by exact prefixLift 1730388
  have htrace : WordTrace (prefixWord ++ tailWord_1730388) baseStart_1730388 baseEnd_1730388 := by
    simpa [prefixWord, tailWord_1730388, baseEnd_1730388] using wordTrace_append hprefix tailTrace_1730388
  have hstable : (prefixWord ++ tailWord_1730388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730388).length < 2 ^ (prefixWord ++ tailWord_1730388).sum := by decide
  have hdescent : baseEnd_1730388 < baseStart_1730388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730493 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1730493 : Nat := 118140960795 + 1730493 * 2 ^ 59
def prefixEnd_1730493 : Nat := 4983230072969 + 3 ^ 40 * 1730493 * 2
def baseEnd_1730493 : Nat := 592383118827335447919409

theorem tailTrace_1730493 : CollatzResearch.WordTrace tailWord_1730493 prefixEnd_1730493 592383118827335447919409 := by
  unfold tailWord_1730493
  simp only [CollatzResearch.WordTrace]
  refine ⟨63116264919726880519996133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42077509946484587013330755 63116264919726880519996133)
  ·
    refine ⟨11834299672448790097499275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63116264919726880519996133 11834299672448790097499275)
    ·
      refine ⟨17751449508673185146248913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834299672448790097499275 17751449508673185146248913)
      ·
        refine ⟨13313587131504888859686685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17751449508673185146248913 13313587131504888859686685)
        ·
          refine ⟨4992595174314333322382507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13313587131504888859686685 4992595174314333322382507)
          ·
            refine ⟨7488892761471499983573761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992595174314333322382507 7488892761471499983573761)
            ·
              refine ⟨5616669571103624987680321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7488892761471499983573761 5616669571103624987680321)
              ·
                refine ⟨4212502178327718740760241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616669571103624987680321 4212502178327718740760241)
                ·
                  refine ⟨3159376633745789055570181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4212502178327718740760241 3159376633745789055570181)
                  ·
                    refine ⟨592383118827335447919409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159376633745789055570181 592383118827335447919409)
                    ·
                      rfl

theorem cell22_1730493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1730493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730493 prefixEnd_1730493 := by exact prefixLift 1730493
  have htrace : WordTrace (prefixWord ++ tailWord_1730493) baseStart_1730493 baseEnd_1730493 := by
    simpa [prefixWord, tailWord_1730493, baseEnd_1730493] using wordTrace_append hprefix tailTrace_1730493
  have hstable : (prefixWord ++ tailWord_1730493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730493).length < 2 ^ (prefixWord ++ tailWord_1730493).sum := by decide
  have hdescent : baseEnd_1730493 < baseStart_1730493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730508 : List Nat := [2, 2, 1, 4, 1, 4, 1, 7]
def baseStart_1730508 : Nat := 118140960795 + 1730508 * 2 ^ 59
def prefixEnd_1730508 : Nat := 4983230072969 + 3 ^ 40 * 1730508 * 2
def baseEnd_1730508 : Nat := 65820917070431156532707

theorem tailTrace_1730508 : CollatzResearch.WordTrace tailWord_1730508 prefixEnd_1730508 65820917070431156532707 := by
  unfold tailWord_1730508
  simp only [CollatzResearch.WordTrace]
  refine ⟨31558406007336269040896089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42077874676448358721194785 31558406007336269040896089)
  ·
    refine ⟨23668804505502201780672067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31558406007336269040896089 23668804505502201780672067)
    ·
      refine ⟨35503206758253302671008101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23668804505502201780672067 35503206758253302671008101)
      ·
        refine ⟨6656851267172494250814019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35503206758253302671008101 6656851267172494250814019)
        ·
          refine ⟨9985276900758741376221029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656851267172494250814019 9985276900758741376221029)
          ·
            refine ⟨1872239418892264008041443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9985276900758741376221029 1872239418892264008041443)
            ·
              refine ⟨2808359128338396012062165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872239418892264008041443 2808359128338396012062165)
              ·
                refine ⟨65820917070431156532707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2808359128338396012062165 65820917070431156532707)
                ·
                  rfl

theorem cell22_1730508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 7].length) (baseStart_1730508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730508 prefixEnd_1730508 := by exact prefixLift 1730508
  have htrace : WordTrace (prefixWord ++ tailWord_1730508) baseStart_1730508 baseEnd_1730508 := by
    simpa [prefixWord, tailWord_1730508, baseEnd_1730508] using wordTrace_append hprefix tailTrace_1730508
  have hstable : (prefixWord ++ tailWord_1730508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730508).length < 2 ^ (prefixWord ++ tailWord_1730508).sum := by decide
  have hdescent : baseEnd_1730508 < baseStart_1730508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730525 : List Nat := [1, 4, 3, 1, 3, 1, 3, 6]
def baseStart_1730525 : Nat := 118140960795 + 1730525 * 2 ^ 59
def prefixEnd_1730525 : Nat := 4983230072969 + 3 ^ 40 * 1730525 * 2
def baseEnd_1730525 : Nat := 65821563675699781235479

theorem tailTrace_1730525 : CollatzResearch.WordTrace tailWord_1730525 prefixEnd_1730525 65821563675699781235479 := by
  unfold tailWord_1730525
  simp only [CollatzResearch.WordTrace]
  refine ⟨63117432055610949985161029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42078288037073966656774019 63117432055610949985161029)
  ·
    refine ⟨11834518510427053122217693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63117432055610949985161029 11834518510427053122217693)
    ·
      refine ⟨4437944441410144920831635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11834518510427053122217693 4437944441410144920831635)
      ·
        refine ⟨6656916662115217381247453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4437944441410144920831635 6656916662115217381247453)
        ·
          refine ⟨2496343748293206517967795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6656916662115217381247453 2496343748293206517967795)
          ·
            refine ⟨3744515622439809776951693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496343748293206517967795 3744515622439809776951693)
            ·
              refine ⟨1404193358414928666356885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3744515622439809776951693 1404193358414928666356885)
              ·
                refine ⟨65821563675699781235479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1404193358414928666356885 65821563675699781235479)
                ·
                  rfl

theorem cell22_1730525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 6].length) (baseStart_1730525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730525 prefixEnd_1730525 := by exact prefixLift 1730525
  have htrace : WordTrace (prefixWord ++ tailWord_1730525) baseStart_1730525 baseEnd_1730525 := by
    simpa [prefixWord, tailWord_1730525, baseEnd_1730525] using wordTrace_append hprefix tailTrace_1730525
  have hstable : (prefixWord ++ tailWord_1730525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730525).length < 2 ^ (prefixWord ++ tailWord_1730525).sum := by decide
  have hdescent : baseEnd_1730525 < baseStart_1730525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730536 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 7]
def baseStart_1730536 : Nat := 118140960795 + 1730536 * 2 ^ 59
def prefixEnd_1730536 : Nat := 4983230072969 + 3 ^ 40 * 1730536 * 2
def baseEnd_1730536 : Nat := 197465946202032556364759

theorem tailTrace_1730536 : CollatzResearch.WordTrace tailWord_1730536 prefixEnd_1730536 197465946202032556364759 := by
  unfold tailWord_1730536
  simp only [CollatzResearch.WordTrace]
  refine ⟨31558916629285549431905731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42078555505714065909207641 31558916629285549431905731)
  ·
    refine ⟨47338374943928324147858597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31558916629285549431905731 47338374943928324147858597)
    ·
      refine ⟨8875945301986560777723487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47338374943928324147858597 8875945301986560777723487)
      ·
        refine ⟨13313917952979841166585231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8875945301986560777723487 13313917952979841166585231)
        ·
          refine ⟨19970876929469761749877847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13313917952979841166585231 19970876929469761749877847)
          ·
            refine ⟨29956315394204642624816771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19970876929469761749877847 29956315394204642624816771)
            ·
              refine ⟨44934473091306963937225157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29956315394204642624816771 44934473091306963937225157)
              ·
                refine ⟨8425213704620055738229717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44934473091306963937225157 8425213704620055738229717)
                ·
                  refine ⟨197465946202032556364759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8425213704620055738229717 197465946202032556364759)
                  ·
                    rfl

theorem cell22_1730536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_1730536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730536 prefixEnd_1730536 := by exact prefixLift 1730536
  have htrace : WordTrace (prefixWord ++ tailWord_1730536) baseStart_1730536 baseEnd_1730536 := by
    simpa [prefixWord, tailWord_1730536, baseEnd_1730536] using wordTrace_append hprefix tailTrace_1730536
  have hstable : (prefixWord ++ tailWord_1730536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730536).length < 2 ^ (prefixWord ++ tailWord_1730536).sum := by decide
  have hdescent : baseEnd_1730536 < baseStart_1730536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730553 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 5]
def baseStart_1730553 : Nat := 118140960795 + 1730553 * 2 ^ 59
def prefixEnd_1730553 : Nat := 4983230072969 + 3 ^ 40 * 1730553 * 2
def baseEnd_1730553 : Nat := 197467886017838430473075

theorem tailTrace_1730553 : CollatzResearch.WordTrace tailWord_1730553 prefixEnd_1730553 197467886017838430473075 := by
  unfold tailWord_1730553
  simp only [CollatzResearch.WordTrace]
  refine ⟨63118453299509510767180313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42078968866339673844786875 63118453299509510767180313)
  ·
    refine ⟨47338839974632133075385235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63118453299509510767180313 47338839974632133075385235)
    ·
      refine ⟨71008259961948199613077853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47338839974632133075385235 71008259961948199613077853)
      ·
        refine ⟨26628097485730574854904195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71008259961948199613077853 26628097485730574854904195)
        ·
          refine ⟨39942146228595862282356293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628097485730574854904195 39942146228595862282356293)
          ·
            refine ⟨7489152417861724177941805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39942146228595862282356293 7489152417861724177941805)
            ·
              refine ⟨2808432156698146566728177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7489152417861724177941805 2808432156698146566728177)
              ·
                refine ⟨2106324117523609925046133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808432156698146566728177 2106324117523609925046133)
                ·
                  refine ⟨197467886017838430473075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2106324117523609925046133 197467886017838430473075)
                  ·
                    rfl

theorem cell22_1730553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_1730553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730553 prefixEnd_1730553 := by exact prefixLift 1730553
  have htrace : WordTrace (prefixWord ++ tailWord_1730553) baseStart_1730553 baseEnd_1730553 := by
    simpa [prefixWord, tailWord_1730553, baseEnd_1730553] using wordTrace_append hprefix tailTrace_1730553
  have hstable : (prefixWord ++ tailWord_1730553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730553).length < 2 ^ (prefixWord ++ tailWord_1730553).sum := by decide
  have hdescent : baseEnd_1730553 < baseStart_1730553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730645 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_1730645 : Nat := 118140960795 + 1730645 * 2 ^ 59
def prefixEnd_1730645 : Nat := 4983230072969 + 3 ^ 40 * 1730645 * 2
def baseEnd_1730645 : Nat := 592435151533657718118943

theorem tailTrace_1730645 : CollatzResearch.WordTrace tailWord_1730645 prefixEnd_1730645 592435151533657718118943 := by
  unfold tailWord_1730645
  simp only [CollatzResearch.WordTrace]
  refine ⟨63121808815176210479529389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42081205876784140319686259 63121808815176210479529389)
  ·
    refine ⟨23670678305691078929823521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63121808815176210479529389 23670678305691078929823521)
    ·
      refine ⟨17753008729268309197367641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23670678305691078929823521 17753008729268309197367641)
      ·
        refine ⟨13314756546951231898025731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17753008729268309197367641 13314756546951231898025731)
        ·
          refine ⟨19972134820426847847038597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13314756546951231898025731 19972134820426847847038597)
          ·
            refine ⟨3744775278830033971319737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19972134820426847847038597 3744775278830033971319737)
            ·
              refine ⟨2808581459122525478489803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3744775278830033971319737 2808581459122525478489803)
              ·
                refine ⟨4212872188683788217734705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808581459122525478489803 4212872188683788217734705)
                ·
                  refine ⟨3159654141512841163301029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4212872188683788217734705 3159654141512841163301029)
                  ·
                    refine ⟨592435151533657718118943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159654141512841163301029 592435151533657718118943)
                    ·
                      rfl

theorem cell22_1730645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_1730645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730645 prefixEnd_1730645 := by exact prefixLift 1730645
  have htrace : WordTrace (prefixWord ++ tailWord_1730645) baseStart_1730645 baseEnd_1730645 := by
    simpa [prefixWord, tailWord_1730645, baseEnd_1730645] using wordTrace_append hprefix tailTrace_1730645
  have hstable : (prefixWord ++ tailWord_1730645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730645).length < 2 ^ (prefixWord ++ tailWord_1730645).sum := by decide
  have hdescent : baseEnd_1730645 < baseStart_1730645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730666 : List Nat := [3, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_1730666 : Nat := 118140960795 + 1730666 * 2 ^ 59
def prefixEnd_1730666 : Nat := 4983230072969 + 3 ^ 40 * 1730666 * 2
def baseEnd_1730666 : Nat := 197480780087606887781293

theorem tailTrace_1730666 : CollatzResearch.WordTrace tailWord_1730666 prefixEnd_1730666 197480780087606887781293 := by
  unfold tailWord_1730666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780643687025032766510963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42081716498733420710695901 15780643687025032766510963)
  ·
    refine ⟨23670965530537549149766445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15780643687025032766510963 23670965530537549149766445)
    ·
      refine ⟨8876612073951580931162417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23670965530537549149766445 8876612073951580931162417)
      ·
        refine ⟨6657459055463685698371813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8876612073951580931162417 6657459055463685698371813)
        ·
          refine ⟨1248273572899441068444715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6657459055463685698371813 1248273572899441068444715)
          ·
            refine ⟨1872410359349161602667073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248273572899441068444715 1872410359349161602667073)
            ·
              refine ⟨1404307769511871202000305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872410359349161602667073 1404307769511871202000305)
              ·
                refine ⟨1053230827133903401500229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404307769511871202000305 1053230827133903401500229)
                ·
                  refine ⟨197480780087606887781293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1053230827133903401500229 197480780087606887781293)
                  ·
                    rfl

theorem cell22_1730666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_1730666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730666 prefixEnd_1730666 := by exact prefixLift 1730666
  have htrace : WordTrace (prefixWord ++ tailWord_1730666) baseStart_1730666 baseEnd_1730666 := by
    simpa [prefixWord, tailWord_1730666, baseEnd_1730666] using wordTrace_append hprefix tailTrace_1730666
  have hstable : (prefixWord ++ tailWord_1730666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730666).length < 2 ^ (prefixWord ++ tailWord_1730666).sum := by decide
  have hdescent : baseEnd_1730666 < baseStart_1730666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730722 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1730722 : Nat := 118140960795 + 1730722 * 2 ^ 59
def prefixEnd_1730722 : Nat := 4983230072969 + 3 ^ 40 * 1730722 * 2
def baseEnd_1730722 : Nat := 197487170069085061314569

theorem tailTrace_1730722 : CollatzResearch.WordTrace tailWord_1730722 prefixEnd_1730722 197487170069085061314569 := by
  unfold tailWord_1730722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781154308974313157520605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42083078157264835086721613 15781154308974313157520605)
  ·
    refine ⟨5917932865865367434070227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15781154308974313157520605 5917932865865367434070227)
    ·
      refine ⟨8876899298798051151105341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5917932865865367434070227 8876899298798051151105341)
      ·
        refine ⟨3328837237049269181664503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8876899298798051151105341 3328837237049269181664503)
        ·
          refine ⟨4993255855573903772496755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328837237049269181664503 4993255855573903772496755)
          ·
            refine ⟨7489883783360855658745133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993255855573903772496755 7489883783360855658745133)
            ·
              refine ⟨2808706418760320872029425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7489883783360855658745133 2808706418760320872029425)
              ·
                refine ⟨2106529814070240654022069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808706418760320872029425 2106529814070240654022069)
                ·
                  refine ⟨197487170069085061314569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2106529814070240654022069 197487170069085061314569)
                  ·
                    rfl

theorem cell22_1730722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1730722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730722 prefixEnd_1730722 := by exact prefixLift 1730722
  have htrace : WordTrace (prefixWord ++ tailWord_1730722) baseStart_1730722 baseEnd_1730722 := by
    simpa [prefixWord, tailWord_1730722, baseEnd_1730722] using wordTrace_append hprefix tailTrace_1730722
  have hstable : (prefixWord ++ tailWord_1730722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730722).length < 2 ^ (prefixWord ++ tailWord_1730722).sum := by decide
  have hdescent : baseEnd_1730722 < baseStart_1730722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730752 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_1730752 : Nat := 118140960795 + 1730752 * 2 ^ 59
def prefixEnd_1730752 : Nat := 4983230072969 + 3 ^ 40 * 1730752 * 2
def baseEnd_1730752 : Nat := 592471779820345105693615

theorem tailTrace_1730752 : CollatzResearch.WordTrace tailWord_1730752 prefixEnd_1730752 592471779820345105693615 := by
  unfold tailWord_1730752
  simp only [CollatzResearch.WordTrace]
  refine ⟨31562855712894283876837255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42083807617192378502449673 31562855712894283876837255)
  ·
    refine ⟨47344283569341425815255883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31562855712894283876837255 47344283569341425815255883)
    ·
      refine ⟨71016425354012138722883825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47344283569341425815255883 71016425354012138722883825)
      ·
        refine ⟨53262319015509104042162869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71016425354012138722883825 53262319015509104042162869)
        ·
          refine ⟨4993342407703978503952769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53262319015509104042162869 4993342407703978503952769)
          ·
            refine ⟨3745006805777983877964577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993342407703978503952769 3745006805777983877964577)
            ·
              refine ⟨2808755104333487908473433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745006805777983877964577 2808755104333487908473433)
              ·
                refine ⟨2106566328250115931355075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808755104333487908473433 2106566328250115931355075)
                ·
                  refine ⟨3159849492375173897032613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106566328250115931355075 3159849492375173897032613)
                  ·
                    refine ⟨592471779820345105693615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159849492375173897032613 592471779820345105693615)
                    ·
                      rfl

theorem cell22_1730752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_1730752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730752 prefixEnd_1730752 := by exact prefixLift 1730752
  have htrace : WordTrace (prefixWord ++ tailWord_1730752) baseStart_1730752 baseEnd_1730752 := by
    simpa [prefixWord, tailWord_1730752, baseEnd_1730752] using wordTrace_append hprefix tailTrace_1730752
  have hstable : (prefixWord ++ tailWord_1730752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730752).length < 2 ^ (prefixWord ++ tailWord_1730752).sum := by decide
  have hdescent : baseEnd_1730752 < baseStart_1730752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730763 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 1, 6]
def baseStart_1730763 : Nat := 118140960795 + 1730763 * 2 ^ 59
def prefixEnd_1730763 : Nat := 4983230072969 + 3 ^ 40 * 1730763 * 2
def baseEnd_1730763 : Nat := 592475545345144743668581

theorem tailTrace_1730763 : CollatzResearch.WordTrace tailWord_1730763 prefixEnd_1730763 592475545345144743668581 := by
  unfold tailWord_1730763
  simp only [CollatzResearch.WordTrace]
  refine ⟨63126112628748716632324943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42084075085832477754883295 63126112628748716632324943)
  ·
    refine ⟨94689168943123074948487415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63126112628748716632324943 94689168943123074948487415)
    ·
      refine ⟨142033753414684612422731123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94689168943123074948487415 142033753414684612422731123)
      ·
        refine ⟨213050630122026918634096685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142033753414684612422731123 213050630122026918634096685)
        ·
          refine ⟨79893986295760094487786257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213050630122026918634096685 79893986295760094487786257)
          ·
            refine ⟨59920489721820070865839693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79893986295760094487786257 59920489721820070865839693)
            ·
              refine ⟨22470183645682526574689885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59920489721820070865839693 22470183645682526574689885)
              ·
                refine ⟨8426318867130947465508707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22470183645682526574689885 8426318867130947465508707)
                ·
                  refine ⟨12639478300696421198263061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8426318867130947465508707 12639478300696421198263061)
                  ·
                    refine ⟨592475545345144743668581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12639478300696421198263061 592475545345144743668581)
                    ·
                      rfl

theorem cell22_1730763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_1730763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730763 prefixEnd_1730763 := by exact prefixLift 1730763
  have htrace : WordTrace (prefixWord ++ tailWord_1730763) baseStart_1730763 baseEnd_1730763 := by
    simpa [prefixWord, tailWord_1730763, baseEnd_1730763] using wordTrace_append hprefix tailTrace_1730763
  have hstable : (prefixWord ++ tailWord_1730763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730763).length < 2 ^ (prefixWord ++ tailWord_1730763).sum := by decide
  have hdescent : baseEnd_1730763 < baseStart_1730763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730778 : List Nat := [3, 1, 1, 2, 2, 1, 12]
def baseStart_1730778 : Nat := 118140960795 + 1730778 * 2 ^ 59
def prefixEnd_1730778 : Nat := 4983230072969 + 3 ^ 40 * 1730778 * 2
def baseEnd_1730778 : Nat := 21943728894507026094205

theorem tailTrace_1730778 : CollatzResearch.WordTrace tailWord_1730778 prefixEnd_1730778 21943728894507026094205 := by
  unfold tailWord_1730778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781664930923593548530247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42084439815796249462747325 15781664930923593548530247)
  ·
    refine ⟨23672497396385390322795371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15781664930923593548530247 23672497396385390322795371)
    ·
      refine ⟨35508746094578085484193057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23672497396385390322795371 35508746094578085484193057)
      ·
        refine ⟨26631559570933564113144793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35508746094578085484193057 26631559570933564113144793)
        ·
          refine ⟨19973669678200173084858595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26631559570933564113144793 19973669678200173084858595)
          ·
            refine ⟨29960504517300259627287893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19973669678200173084858595 29960504517300259627287893)
            ·
              refine ⟨21943728894507026094205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29960504517300259627287893 21943728894507026094205)
              ·
                rfl

theorem cell22_1730778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 12].length) (baseStart_1730778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730778 prefixEnd_1730778 := by exact prefixLift 1730778
  have htrace : WordTrace (prefixWord ++ tailWord_1730778) baseStart_1730778 baseEnd_1730778 := by
    simpa [prefixWord, tailWord_1730778, baseEnd_1730778] using wordTrace_append hprefix tailTrace_1730778
  have hstable : (prefixWord ++ tailWord_1730778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730778).length < 2 ^ (prefixWord ++ tailWord_1730778).sum := by decide
  have hdescent : baseEnd_1730778 < baseStart_1730778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730799 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 2, 3]
def baseStart_1730799 : Nat := 118140960795 + 1730799 * 2 ^ 59
def prefixEnd_1730799 : Nat := 4983230072969 + 3 ^ 40 * 1730799 * 2
def baseEnd_1730799 : Nat := 592487868880852649768471

theorem tailTrace_1730799 : CollatzResearch.WordTrace tailWord_1730799 prefixEnd_1730799 592487868880852649768471 := by
  unfold tailWord_1730799
  simp only [CollatzResearch.WordTrace]
  refine ⟨63127425656618294780635451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42084950437745529853756967 63127425656618294780635451)
  ·
    refine ⟨94691138484927442170953177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63127425656618294780635451 94691138484927442170953177)
    ·
      refine ⟨71018353863695581628214883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94691138484927442170953177 71018353863695581628214883)
      ·
        refine ⟨106527530795543372442322325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71018353863695581628214883 106527530795543372442322325)
        ·
          refine ⟨4993478006041095583233859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106527530795543372442322325 4993478006041095583233859)
          ·
            refine ⟨7490217009061643374850789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993478006041095583233859 7490217009061643374850789)
            ·
              refine ⟨1404415689199058132784523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7490217009061643374850789 1404415689199058132784523)
              ·
                refine ⟨2106623533798587199176785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404415689199058132784523 2106623533798587199176785)
                ·
                  refine ⟨1579967650348940399382589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106623533798587199176785 1579967650348940399382589)
                  ·
                    refine ⟨592487868880852649768471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1579967650348940399382589 592487868880852649768471)
                    ·
                      rfl

theorem cell22_1730799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_1730799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730799 prefixEnd_1730799 := by exact prefixLift 1730799
  have htrace : WordTrace (prefixWord ++ tailWord_1730799) baseStart_1730799 baseEnd_1730799 := by
    simpa [prefixWord, tailWord_1730799, baseEnd_1730799] using wordTrace_append hprefix tailTrace_1730799
  have hstable : (prefixWord ++ tailWord_1730799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730799).length < 2 ^ (prefixWord ++ tailWord_1730799).sum := by decide
  have hdescent : baseEnd_1730799 < baseStart_1730799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730861 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1730861 : Nat := 118140960795 + 1730861 * 2 ^ 59
def prefixEnd_1730861 : Nat := 4983230072969 + 3 ^ 40 * 1730861 * 2
def baseEnd_1730861 : Nat := 592509092747905154718281

theorem tailTrace_1730861 : CollatzResearch.WordTrace tailWord_1730861 prefixEnd_1730861 592509092747905154718281 := by
  unfold tailWord_1730861
  simp only [CollatzResearch.WordTrace]
  refine ⟨63129686982393679369392437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42086457988262452912928291 63129686982393679369392437)
  ·
    refine ⟨5918408154599407440880541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63129686982393679369392437 5918408154599407440880541)
    ·
      refine ⟨2219403057974777790330203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5918408154599407440880541 2219403057974777790330203)
      ·
        refine ⟨3329104586962166685495305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219403057974777790330203 3329104586962166685495305)
        ·
          refine ⟨2496828440221625014121479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329104586962166685495305 2496828440221625014121479)
          ·
            refine ⟨3745242660332437521182219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496828440221625014121479 3745242660332437521182219)
            ·
              refine ⟨5617863990498656281773329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745242660332437521182219 5617863990498656281773329)
              ·
                refine ⟨4213397992873992211329997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5617863990498656281773329 4213397992873992211329997)
                ·
                  refine ⟨1580024247327747079248749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4213397992873992211329997 1580024247327747079248749)
                  ·
                    refine ⟨592509092747905154718281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580024247327747079248749 592509092747905154718281)
                    ·
                      rfl

theorem cell22_1730861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1730861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730861 prefixEnd_1730861 := by exact prefixLift 1730861
  have htrace : WordTrace (prefixWord ++ tailWord_1730861) baseStart_1730861 baseEnd_1730861 := by
    simpa [prefixWord, tailWord_1730861, baseEnd_1730861] using wordTrace_append hprefix tailTrace_1730861
  have hstable : (prefixWord ++ tailWord_1730861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730861).length < 2 ^ (prefixWord ++ tailWord_1730861).sum := by decide
  have hdescent : baseEnd_1730861 < baseStart_1730861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730887 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1730887 : Nat := 118140960795 + 1730887 * 2 ^ 59
def prefixEnd_1730887 : Nat := 4983230072969 + 3 ^ 40 * 1730887 * 2
def baseEnd_1730887 : Nat := 592517993079249753568201

theorem tailTrace_1730887 : CollatzResearch.WordTrace tailWord_1730887 prefixEnd_1730887 592517993079249753568201 := by
  unfold tailWord_1730887
  simp only [CollatzResearch.WordTrace]
  refine ⟨63130635280299485809838915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42087090186866323873225943 63130635280299485809838915)
  ·
    refine ⟨94695952920449228714758373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63130635280299485809838915 94695952920449228714758373)
    ·
      refine ⟨17755491172584230384017195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94695952920449228714758373 17755491172584230384017195)
      ·
        refine ⟨26633236758876345576025793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17755491172584230384017195 26633236758876345576025793)
        ·
          refine ⟨19974927569157259182019345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26633236758876345576025793 19974927569157259182019345)
          ·
            refine ⟨14981195676867944386514509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19974927569157259182019345 14981195676867944386514509)
            ·
              refine ⟨5617948378825479144942941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14981195676867944386514509 5617948378825479144942941)
              ·
                refine ⟨2106730642059554679353603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5617948378825479144942941 2106730642059554679353603)
                ·
                  refine ⟨3160095963089332019030405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106730642059554679353603 3160095963089332019030405)
                  ·
                    refine ⟨592517993079249753568201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3160095963089332019030405 592517993079249753568201)
                    ·
                      rfl

theorem cell22_1730887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1730887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730887 prefixEnd_1730887 := by exact prefixLift 1730887
  have htrace : WordTrace (prefixWord ++ tailWord_1730887) baseStart_1730887 baseEnd_1730887 := by
    simpa [prefixWord, tailWord_1730887, baseEnd_1730887] using wordTrace_append hprefix tailTrace_1730887
  have hstable : (prefixWord ++ tailWord_1730887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730887).length < 2 ^ (prefixWord ++ tailWord_1730887).sum := by decide
  have hdescent : baseEnd_1730887 < baseStart_1730887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730915 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 3, 6]
def baseStart_1730915 : Nat := 118140960795 + 1730915 * 2 ^ 59
def prefixEnd_1730915 : Nat := 4983230072969 + 3 ^ 40 * 1730915 * 2
def baseEnd_1730915 : Nat := 592527578051467013868115

theorem tailTrace_1730915 : CollatzResearch.WordTrace tailWord_1730915 prefixEnd_1730915 592527578051467013868115 := by
  unfold tailWord_1730915
  simp only [CollatzResearch.WordTrace]
  refine ⟨63131656524198046591858199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42087771016132031061238799 63131656524198046591858199)
  ·
    refine ⟨94697484786297069887787299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63131656524198046591858199 94697484786297069887787299)
    ·
      refine ⟨142046227179445604831680949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94697484786297069887787299 142046227179445604831680949)
      ·
        refine ⟨13316833798073025452970089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142046227179445604831680949 13316833798073025452970089)
        ·
          refine ⟨9987625348554769089727567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13316833798073025452970089 9987625348554769089727567)
          ·
            refine ⟨14981438022832153634591351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987625348554769089727567 14981438022832153634591351)
            ·
              refine ⟨22472157034248230451887027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14981438022832153634591351 22472157034248230451887027)
              ·
                refine ⟨33708235551372345677830541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22472157034248230451887027 33708235551372345677830541)
                ·
                  refine ⟨12640588331764629629186453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33708235551372345677830541 12640588331764629629186453)
                  ·
                    refine ⟨592527578051467013868115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12640588331764629629186453 592527578051467013868115)
                    ·
                      rfl

theorem cell22_1730915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_1730915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730915 prefixEnd_1730915 := by exact prefixLift 1730915
  have htrace : WordTrace (prefixWord ++ tailWord_1730915) baseStart_1730915 baseEnd_1730915 := by
    simpa [prefixWord, tailWord_1730915, baseEnd_1730915] using wordTrace_append hprefix tailTrace_1730915
  have hstable : (prefixWord ++ tailWord_1730915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730915).length < 2 ^ (prefixWord ++ tailWord_1730915).sum := by decide
  have hdescent : baseEnd_1730915 < baseStart_1730915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730917 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_1730917 : Nat := 118140960795 + 1730917 * 2 ^ 59
def prefixEnd_1730917 : Nat := 4983230072969 + 3 ^ 40 * 1730917 * 2
def baseEnd_1730917 : Nat := 592528262692339675318109

theorem tailTrace_1730917 : CollatzResearch.WordTrace tailWord_1730917 prefixEnd_1730917 592528262692339675318109 := by
  unfold tailWord_1730917
  simp only [CollatzResearch.WordTrace]
  refine ⟨63131729470190800933431005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42087819646793867288954003 63131729470190800933431005)
  ·
    refine ⟨23674398551321550350036627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63131729470190800933431005 23674398551321550350036627)
    ·
      refine ⟨35511597826982325525054941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23674398551321550350036627 35511597826982325525054941)
      ·
        refine ⟨13316849185118372071895603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35511597826982325525054941 13316849185118372071895603)
        ·
          refine ⟨19975273777677558107843405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13316849185118372071895603 19975273777677558107843405)
          ·
            refine ⟨7490727666629084290441277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19975273777677558107843405 7490727666629084290441277)
            ·
              refine ⟨2809022874985906608915479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7490727666629084290441277 2809022874985906608915479)
              ·
                refine ⟨4213534312478859913373219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809022874985906608915479 4213534312478859913373219)
                ·
                  refine ⟨6320301468718289870059829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213534312478859913373219 6320301468718289870059829)
                  ·
                    refine ⟨592528262692339675318109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6320301468718289870059829 592528262692339675318109)
                    ·
                      rfl

theorem cell22_1730917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_1730917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730917 prefixEnd_1730917 := by exact prefixLift 1730917
  have htrace : WordTrace (prefixWord ++ tailWord_1730917) baseStart_1730917 baseEnd_1730917 := by
    simpa [prefixWord, tailWord_1730917, baseEnd_1730917] using wordTrace_append hprefix tailTrace_1730917
  have hstable : (prefixWord ++ tailWord_1730917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730917).length < 2 ^ (prefixWord ++ tailWord_1730917).sum := by decide
  have hdescent : baseEnd_1730917 < baseStart_1730917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730947 : List Nat := [1, 1, 1, 3, 6, 2, 8]
def baseStart_1730947 : Nat := 118140960795 + 1730947 * 2 ^ 59
def prefixEnd_1730947 : Nat := 4983230072969 + 3 ^ 40 * 1730947 * 2
def baseEnd_1730947 : Nat := 21945871566867762854371

theorem tailTrace_1730947 : CollatzResearch.WordTrace tailWord_1730947 prefixEnd_1730947 21945871566867762854371 := by
  unfold tailWord_1730947
  simp only [CollatzResearch.WordTrace]
  refine ⟨63132823660082116057023095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42088549106721410704682063 63132823660082116057023095)
  ·
    refine ⟨94699235490123174085534643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63132823660082116057023095 94699235490123174085534643)
    ·
      refine ⟨142048853235184761128301965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94699235490123174085534643 142048853235184761128301965)
      ·
        refine ⟨53268319963194285423113237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142048853235184761128301965 53268319963194285423113237)
        ·
          refine ⟨2496952498274732129208433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53268319963194285423113237 2496952498274732129208433)
          ·
            refine ⟨1872714373706049096906325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496952498274732129208433 1872714373706049096906325)
            ·
              refine ⟨21945871566867762854371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1872714373706049096906325 21945871566867762854371)
              ·
                rfl

theorem cell22_1730947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 8].length) (baseStart_1730947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730947 prefixEnd_1730947 := by exact prefixLift 1730947
  have htrace : WordTrace (prefixWord ++ tailWord_1730947) baseStart_1730947 baseEnd_1730947 := by
    simpa [prefixWord, tailWord_1730947, baseEnd_1730947] using wordTrace_append hprefix tailTrace_1730947
  have hstable : (prefixWord ++ tailWord_1730947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730947).length < 2 ^ (prefixWord ++ tailWord_1730947).sum := by decide
  have hdescent : baseEnd_1730947 < baseStart_1730947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730964 : List Nat := [2, 4, 2, 1, 3, 1, 2, 7]
def baseStart_1730964 : Nat := 118140960795 + 1730964 * 2 ^ 59
def prefixEnd_1730964 : Nat := 4983230072969 + 3 ^ 40 * 1730964 * 2
def baseEnd_1730964 : Nat := 65838261305871913265885

theorem tailTrace_1730964 : CollatzResearch.WordTrace tailWord_1730964 prefixEnd_1730964 65838261305871913265885 := by
  unfold tailWord_1730964
  simp only [CollatzResearch.WordTrace]
  refine ⟨31566721850510263980195973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42088962467347018640261297 31566721850510263980195973)
  ·
    refine ⟨5918760346970674496286745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31566721850510263980195973 5918760346970674496286745)
    ·
      refine ⟨4439070260228005872215059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5918760346970674496286745 4439070260228005872215059)
      ·
        refine ⟨6658605390342008808322589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439070260228005872215059 6658605390342008808322589)
        ·
          refine ⟨2496977021378253303120971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6658605390342008808322589 2496977021378253303120971)
          ·
            refine ⟨3745465532067379954681457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496977021378253303120971 3745465532067379954681457)
            ·
              refine ⟨2809099149050534966011093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745465532067379954681457 2809099149050534966011093)
              ·
                refine ⟨65838261305871913265885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2809099149050534966011093 65838261305871913265885)
                ·
                  rfl

theorem cell22_1730964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 7].length) (baseStart_1730964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730964 prefixEnd_1730964 := by exact prefixLift 1730964
  have htrace : WordTrace (prefixWord ++ tailWord_1730964) baseStart_1730964 baseEnd_1730964 := by
    simpa [prefixWord, tailWord_1730964, baseEnd_1730964] using wordTrace_append hprefix tailTrace_1730964
  have hstable : (prefixWord ++ tailWord_1730964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730964).length < 2 ^ (prefixWord ++ tailWord_1730964).sum := by decide
  have hdescent : baseEnd_1730964 < baseStart_1730964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1730968 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 2, 3]
def baseStart_1730968 : Nat := 118140960795 + 1730968 * 2 ^ 59
def prefixEnd_1730968 : Nat := 4983230072969 + 3 ^ 40 * 1730968 * 2
def baseEnd_1730968 : Nat := 592545721034592542292953

theorem tailTrace_1730968 : CollatzResearch.WordTrace tailWord_1730968 prefixEnd_1730968 592545721034592542292953 := by
  unfold tailWord_1730968
  simp only [CollatzResearch.WordTrace]
  refine ⟨31566794796503018321768779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42089059728670691095691705 31566794796503018321768779)
  ·
    refine ⟨47350192194754527482653169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31566794796503018321768779 47350192194754527482653169)
    ·
      refine ⟨35512644146065895611989877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47350192194754527482653169 35512644146065895611989877)
      ·
        refine ⟨3329310388693677713624051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35512644146065895611989877 3329310388693677713624051)
        ·
          refine ⟨4993965583040516570436077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329310388693677713624051 4993965583040516570436077)
          ·
            refine ⟨1872737093640193713913529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4993965583040516570436077 1872737093640193713913529)
            ·
              refine ⟨1404552820230145285435147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872737093640193713913529 1404552820230145285435147)
              ·
                refine ⟨2106829230345217928152721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404552820230145285435147 2106829230345217928152721)
                ·
                  refine ⟨1580121922758913446114541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106829230345217928152721 1580121922758913446114541)
                  ·
                    refine ⟨592545721034592542292953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580121922758913446114541 592545721034592542292953)
                    ·
                      rfl

theorem cell22_1730968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_1730968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1730968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1730968 prefixEnd_1730968 := by exact prefixLift 1730968
  have htrace : WordTrace (prefixWord ++ tailWord_1730968) baseStart_1730968 baseEnd_1730968 := by
    simpa [prefixWord, tailWord_1730968, baseEnd_1730968] using wordTrace_append hprefix tailTrace_1730968
  have hstable : (prefixWord ++ tailWord_1730968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1730968).length < 2 ^ (prefixWord ++ tailWord_1730968).sum := by decide
  have hdescent : baseEnd_1730968 < baseStart_1730968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1730968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731052 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_1731052 : Nat := 118140960795 + 1731052 * 2 ^ 59
def prefixEnd_1731052 : Nat := 4983230072969 + 3 ^ 40 * 1731052 * 2
def baseEnd_1731052 : Nat := 592574475951244323192695

theorem tailTrace_1731052 : CollatzResearch.WordTrace tailWord_1731052 prefixEnd_1731052 592574475951244323192695 := by
  unfold tailWord_1731052
  simp only [CollatzResearch.WordTrace]
  refine ⟨31568326662350859494797705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42091102216467812659730273 31568326662350859494797705)
  ·
    refine ⟨23676244996763144621098279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31568326662350859494797705 23676244996763144621098279)
    ·
      refine ⟨35514367495144716931647419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23676244996763144621098279 35514367495144716931647419)
      ·
        refine ⟨53271551242717075397471129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35514367495144716931647419 53271551242717075397471129)
        ·
          refine ⟨39953663432037806548103347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53271551242717075397471129 39953663432037806548103347)
          ·
            refine ⟨59930495148056709822155021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39953663432037806548103347 59930495148056709822155021)
            ·
              refine ⟨22473935680521266183308133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59930495148056709822155021 22473935680521266183308133)
              ·
                refine ⟨4213862940097737409370275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22473935680521266183308133 4213862940097737409370275)
                ·
                  refine ⟨6320794410146606114055413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213862940097737409370275 6320794410146606114055413)
                  ·
                    refine ⟨592574475951244323192695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6320794410146606114055413 592574475951244323192695)
                    ·
                      rfl

theorem cell22_1731052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_1731052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731052 prefixEnd_1731052 := by exact prefixLift 1731052
  have htrace : WordTrace (prefixWord ++ tailWord_1731052) baseStart_1731052 baseEnd_1731052 := by
    simpa [prefixWord, tailWord_1731052, baseEnd_1731052] using wordTrace_append hprefix tailTrace_1731052
  have hstable : (prefixWord ++ tailWord_1731052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731052).length < 2 ^ (prefixWord ++ tailWord_1731052).sum := by decide
  have hdescent : baseEnd_1731052 < baseStart_1731052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731069 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1731069 : Nat := 118140960795 + 1731069 * 2 ^ 59
def prefixEnd_1731069 : Nat := 4983230072969 + 3 ^ 40 * 1731069 * 2
def baseEnd_1731069 : Nat := 592580295398661945517643

theorem tailTrace_1731069 : CollatzResearch.WordTrace tailWord_1731069 prefixEnd_1731069 592580295398661945517643 := by
  unfold tailWord_1731069
  simp only [CollatzResearch.WordTrace]
  refine ⟨63137273365640130892964261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42091515577093420595309507 63137273365640130892964261)
  ·
    refine ⟨11838238756057524542430799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63137273365640130892964261 11838238756057524542430799)
    ·
      refine ⟨17757358134086286813646199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11838238756057524542430799 17757358134086286813646199)
      ·
        refine ⟨26636037201129430220469299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17757358134086286813646199 26636037201129430220469299)
        ·
          refine ⟨39954055801694145330703949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26636037201129430220469299 39954055801694145330703949)
          ·
            refine ⟨14982770925635304499013981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39954055801694145330703949 14982770925635304499013981)
            ·
              refine ⟨5618539097113239187130243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14982770925635304499013981 5618539097113239187130243)
              ·
                refine ⟨8427808645669858780695365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618539097113239187130243 8427808645669858780695365)
                ·
                  refine ⟨1580214121063098521380381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8427808645669858780695365 1580214121063098521380381)
                  ·
                    refine ⟨592580295398661945517643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580214121063098521380381 592580295398661945517643)
                    ·
                      rfl

theorem cell22_1731069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1731069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731069 prefixEnd_1731069 := by exact prefixLift 1731069
  have htrace : WordTrace (prefixWord ++ tailWord_1731069) baseStart_1731069 baseEnd_1731069 := by
    simpa [prefixWord, tailWord_1731069, baseEnd_1731069] using wordTrace_append hprefix tailTrace_1731069
  have hstable : (prefixWord ++ tailWord_1731069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731069).length < 2 ^ (prefixWord ++ tailWord_1731069).sum := by decide
  have hdescent : baseEnd_1731069 < baseStart_1731069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731082 : List Nat := [3, 1, 2, 2, 2, 1, 2, 9]
def baseStart_1731082 : Nat := 118140960795 + 1731082 * 2 ^ 59
def prefixEnd_1731082 : Nat := 4983230072969 + 3 ^ 40 * 1731082 * 2
def baseEnd_1731082 : Nat := 65842749507148249438067

theorem tailTrace_1731082 : CollatzResearch.WordTrace tailWord_1731082 prefixEnd_1731082 65842749507148249438067 := by
  unfold tailWord_1731082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15784436878648258528296875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42091831676395356075458333 15784436878648258528296875)
  ·
    refine ⟨23676655317972387792445313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15784436878648258528296875 23676655317972387792445313)
    ·
      refine ⟨17757491488479290844333985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23676655317972387792445313 17757491488479290844333985)
      ·
        refine ⟨13318118616359468133250489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17757491488479290844333985 13318118616359468133250489)
        ·
          refine ⟨9988588962269601099937867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13318118616359468133250489 9988588962269601099937867)
          ·
            refine ⟨14982883443404401649906801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9988588962269601099937867 14982883443404401649906801)
            ·
              refine ⟨11237162582553301237430101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14982883443404401649906801 11237162582553301237430101)
              ·
                refine ⟨65842749507148249438067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11237162582553301237430101 65842749507148249438067)
                ·
                  rfl

theorem cell22_1731082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_1731082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731082 prefixEnd_1731082 := by exact prefixLift 1731082
  have htrace : WordTrace (prefixWord ++ tailWord_1731082) baseStart_1731082 baseEnd_1731082 := by
    simpa [prefixWord, tailWord_1731082, baseEnd_1731082] using wordTrace_append hprefix tailTrace_1731082
  have hstable : (prefixWord ++ tailWord_1731082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731082).length < 2 ^ (prefixWord ++ tailWord_1731082).sum := by decide
  have hdescent : baseEnd_1731082 < baseStart_1731082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731086 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_1731086 : Nat := 118140960795 + 1731086 * 2 ^ 59
def prefixEnd_1731086 : Nat := 4983230072969 + 3 ^ 40 * 1731086 * 2
def baseEnd_1731086 : Nat := 592586114846079567842591

theorem tailTrace_1731086 : CollatzResearch.WordTrace tailWord_1731086 prefixEnd_1731086 592586114846079567842591 := by
  unfold tailWord_1731086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892236675822317849541639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42091928937719028530888741 7892236675822317849541639)
  ·
    refine ⟨11838355013733476774312459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7892236675822317849541639 11838355013733476774312459)
    ·
      refine ⟨17757532520600215161468689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11838355013733476774312459 17757532520600215161468689)
      ·
        refine ⟨13318149390450161371101517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17757532520600215161468689 13318149390450161371101517)
        ·
          refine ⟨4994306021418810514163069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13318149390450161371101517 4994306021418810514163069)
          ·
            refine ⟨1872864758032053942811151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4994306021418810514163069 1872864758032053942811151)
            ·
              refine ⟨2809297137048080914216727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872864758032053942811151 2809297137048080914216727)
              ·
                refine ⟨4213945705572121371325091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809297137048080914216727 4213945705572121371325091)
                ·
                  refine ⟨6320918558358182056987637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213945705572121371325091 6320918558358182056987637)
                  ·
                    refine ⟨592586114846079567842591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6320918558358182056987637 592586114846079567842591)
                    ·
                      rfl

theorem cell22_1731086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_1731086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731086 prefixEnd_1731086 := by exact prefixLift 1731086
  have htrace : WordTrace (prefixWord ++ tailWord_1731086) baseStart_1731086 baseEnd_1731086 := by
    simpa [prefixWord, tailWord_1731086, baseEnd_1731086] using wordTrace_append hprefix tailTrace_1731086
  have hstable : (prefixWord ++ tailWord_1731086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731086).length < 2 ^ (prefixWord ++ tailWord_1731086).sum := by decide
  have hdescent : baseEnd_1731086 < baseStart_1731086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731127 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 7]
def baseStart_1731127 : Nat := 118140960795 + 1731127 * 2 ^ 59
def prefixEnd_1731127 : Nat := 4983230072969 + 3 ^ 40 * 1731127 * 2
def baseEnd_1731127 : Nat := 197533383327989709189155

theorem tailTrace_1731127 : CollatzResearch.WordTrace tailWord_1731127 prefixEnd_1731127 197533383327989709189155 := by
  unfold tailWord_1731127
  simp only [CollatzResearch.WordTrace]
  refine ⟨63139388799430006798575635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42092925866286671199050423 63139388799430006798575635)
  ·
    refine ⟨94709083199145010197863453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63139388799430006798575635 94709083199145010197863453)
    ·
      refine ⟨35515906199679378824198795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94709083199145010197863453 35515906199679378824198795)
      ·
        refine ⟨53273859299519068236298193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35515906199679378824198795 53273859299519068236298193)
        ·
          refine ⟨39955394474639301177223645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53273859299519068236298193 39955394474639301177223645)
          ·
            refine ⟨14983272927989737941458867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39955394474639301177223645 14983272927989737941458867)
            ·
              refine ⟨22474909391984606912188301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14983272927989737941458867 22474909391984606912188301)
              ·
                refine ⟨8428091021994227592070613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22474909391984606912188301 8428091021994227592070613)
                ·
                  refine ⟨197533383327989709189155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8428091021994227592070613 197533383327989709189155)
                  ·
                    rfl

theorem cell22_1731127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 7].length) (baseStart_1731127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731127 prefixEnd_1731127 := by exact prefixLift 1731127
  have htrace : WordTrace (prefixWord ++ tailWord_1731127) baseStart_1731127 baseEnd_1731127 := by
    simpa [prefixWord, tailWord_1731127, baseEnd_1731127] using wordTrace_append hprefix tailTrace_1731127
  have hstable : (prefixWord ++ tailWord_1731127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731127).length < 2 ^ (prefixWord ++ tailWord_1731127).sum := by decide
  have hdescent : baseEnd_1731127 < baseStart_1731127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731182 : List Nat := [4, 1, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1731182 : Nat := 118140960795 + 1731182 * 2 ^ 59
def prefixEnd_1731182 : Nat := 4983230072969 + 3 ^ 40 * 1731182 * 2
def baseEnd_1731182 : Nat := 592618977607967317442297

theorem tailTrace_1731182 : CollatzResearch.WordTrace tailWord_1731182 prefixEnd_1731182 592618977607967317442297 := by
  unfold tailWord_1731182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892674351778843898978475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42094263209487167461218533 7892674351778843898978475)
  ·
    refine ⟨11839011527668265848467713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7892674351778843898978475 11839011527668265848467713)
    ·
      refine ⟨8879258645751199386350785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11839011527668265848467713 8879258645751199386350785)
      ·
        refine ⟨6659443984313399539763089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8879258645751199386350785 6659443984313399539763089)
        ·
          refine ⟨4994582988235049654822317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6659443984313399539763089 4994582988235049654822317)
          ·
            refine ⟨1872968620588143620558369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4994582988235049654822317 1872968620588143620558369)
            ·
              refine ⟨1404726465441107715418777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872968620588143620558369 1404726465441107715418777)
              ·
                refine ⟨1053544849080830786564083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404726465441107715418777 1053544849080830786564083)
                ·
                  refine ⟨1580317273621246179846125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053544849080830786564083 1580317273621246179846125)
                  ·
                    refine ⟨592618977607967317442297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580317273621246179846125 592618977607967317442297)
                    ·
                      rfl

theorem cell22_1731182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1731182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731182 prefixEnd_1731182 := by exact prefixLift 1731182
  have htrace : WordTrace (prefixWord ++ tailWord_1731182) baseStart_1731182 baseEnd_1731182 := by
    simpa [prefixWord, tailWord_1731182, baseEnd_1731182] using wordTrace_append hprefix tailTrace_1731182
  have hstable : (prefixWord ++ tailWord_1731182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731182).length < 2 ^ (prefixWord ++ tailWord_1731182).sum := by decide
  have hdescent : baseEnd_1731182 < baseStart_1731182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731255 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 2, 3]
def baseStart_1731255 : Nat := 118140960795 + 1731255 * 2 ^ 59
def prefixEnd_1731255 : Nat := 4983230072969 + 3 ^ 40 * 1731255 * 2
def baseEnd_1731255 : Nat := 592643966999819460367073

theorem tailTrace_1731255 : CollatzResearch.WordTrace tailWord_1731255 prefixEnd_1731255 592643966999819460367073 := by
  unfold tailWord_1731255
  simp only [CollatzResearch.WordTrace]
  refine ⟨63144057342966284659235219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42096038228644189772823479 63144057342966284659235219)
  ·
    refine ⟨94716086014449426988852829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63144057342966284659235219 94716086014449426988852829)
    ·
      refine ⟨35518532255418535120819811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94716086014449426988852829 35518532255418535120819811)
      ·
        refine ⟨53277798383127802681229717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35518532255418535120819811 53277798383127802681229717)
        ·
          refine ⟨2497396799209115750682643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53277798383127802681229717 2497396799209115750682643)
          ·
            refine ⟨3746095198813673626023965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497396799209115750682643 3746095198813673626023965)
            ·
              refine ⟨1404785699555127609758987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3746095198813673626023965 1404785699555127609758987)
              ·
                refine ⟨2107178549332691414638481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404785699555127609758987 2107178549332691414638481)
                ·
                  refine ⟨1580383911999518560978861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2107178549332691414638481 1580383911999518560978861)
                  ·
                    refine ⟨592643966999819460367073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580383911999518560978861 592643966999819460367073)
                    ·
                      rfl

theorem cell22_1731255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_1731255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731255 prefixEnd_1731255 := by exact prefixLift 1731255
  have htrace : WordTrace (prefixWord ++ tailWord_1731255) baseStart_1731255 baseEnd_1731255 := by
    simpa [prefixWord, tailWord_1731255, baseEnd_1731255] using wordTrace_append hprefix tailTrace_1731255
  have hstable : (prefixWord ++ tailWord_1731255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731255).length < 2 ^ (prefixWord ++ tailWord_1731255).sum := by decide
  have hdescent : baseEnd_1731255 < baseStart_1731255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731268 : List Nat := [2, 3, 3, 1, 1, 4, 2, 6]
def baseStart_1731268 : Nat := 118140960795 + 1731268 * 2 ^ 59
def prefixEnd_1731268 : Nat := 4983230072969 + 3 ^ 40 * 1731268 * 2
def baseEnd_1731268 : Nat := 65849824129499084421337

theorem tailTrace_1731268 : CollatzResearch.WordTrace tailWord_1731268 prefixEnd_1731268 65849824129499084421337 := by
  unfold tailWord_1731268
  simp only [CollatzResearch.WordTrace]
  refine ⟨31572265745959593939729229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42096354327946125252972305 31572265745959593939729229)
  ·
    refine ⟨11839599654734847727398461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31572265745959593939729229 11839599654734847727398461)
    ·
      refine ⟨4439849870525567897774423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11839599654734847727398461 4439849870525567897774423)
      ·
        refine ⟨6659774805788351846661635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439849870525567897774423 6659774805788351846661635)
        ·
          refine ⟨9989662208682527769992453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659774805788351846661635 9989662208682527769992453)
          ·
            refine ⟨1873061664127973956873585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9989662208682527769992453 1873061664127973956873585)
            ·
              refine ⟨1404796248095980467655189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873061664127973956873585 1404796248095980467655189)
              ·
                refine ⟨65849824129499084421337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1404796248095980467655189 65849824129499084421337)
                ·
                  rfl

theorem cell22_1731268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 6].length) (baseStart_1731268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731268 prefixEnd_1731268 := by exact prefixLift 1731268
  have htrace : WordTrace (prefixWord ++ tailWord_1731268) baseStart_1731268 baseEnd_1731268 := by
    simpa [prefixWord, tailWord_1731268, baseEnd_1731268] using wordTrace_append hprefix tailTrace_1731268
  have hstable : (prefixWord ++ tailWord_1731268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731268).length < 2 ^ (prefixWord ++ tailWord_1731268).sum := by decide
  have hdescent : baseEnd_1731268 < baseStart_1731268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731343 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 1, 4]
def baseStart_1731343 : Nat := 118140960795 + 1731343 * 2 ^ 59
def prefixEnd_1731343 : Nat := 4983230072969 + 3 ^ 40 * 1731343 * 2
def baseEnd_1731343 : Nat := 592674091198216564166803

theorem tailTrace_1731343 : CollatzResearch.WordTrace tailWord_1731343 prefixEnd_1731343 592674091198216564166803 := by
  unfold tailWord_1731343
  simp only [CollatzResearch.WordTrace]
  refine ⟨63147266966647475688438683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42098177977764983792292455 63147266966647475688438683)
  ·
    refine ⟨94720900449971213532658025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63147266966647475688438683 94720900449971213532658025)
    ·
      refine ⟨71040675337478410149493519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94720900449971213532658025 71040675337478410149493519)
      ·
        refine ⟨106561013006217615224240279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71040675337478410149493519 106561013006217615224240279)
        ·
          refine ⟨159841519509326422836360419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106561013006217615224240279 159841519509326422836360419)
          ·
            refine ⟨239762279263989634254540629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159841519509326422836360419 239762279263989634254540629)
            ·
              refine ⟨1404857105062439263210199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 239762279263989634254540629 1404857105062439263210199)
              ·
                refine ⟨2107285657593658894815299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404857105062439263210199 2107285657593658894815299)
                ·
                  refine ⟨3160928486390488342222949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107285657593658894815299 3160928486390488342222949)
                  ·
                    refine ⟨592674091198216564166803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3160928486390488342222949 592674091198216564166803)
                    ·
                      rfl

theorem cell22_1731343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_1731343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731343 prefixEnd_1731343 := by exact prefixLift 1731343
  have htrace : WordTrace (prefixWord ++ tailWord_1731343) baseStart_1731343 baseEnd_1731343 := by
    simpa [prefixWord, tailWord_1731343, baseEnd_1731343] using wordTrace_append hprefix tailTrace_1731343
  have hstable : (prefixWord ++ tailWord_1731343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731343).length < 2 ^ (prefixWord ++ tailWord_1731343).sum := by decide
  have hdescent : baseEnd_1731343 < baseStart_1731343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731418 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_1731418 : Nat := 118140960795 + 1731418 * 2 ^ 59
def prefixEnd_1731418 : Nat := 4983230072969 + 3 ^ 40 * 1731418 * 2
def baseEnd_1731418 : Nat := 592699765230941368541573

theorem tailTrace_1731418 : CollatzResearch.WordTrace tailWord_1731418 prefixEnd_1731418 592699765230941368541573 := by
  unfold tailWord_1731418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15787500610343940874354727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42100001627583842331612605 15787500610343940874354727)
  ·
    refine ⟨23681250915515911311532091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15787500610343940874354727 23681250915515911311532091)
    ·
      refine ⟨35521876373273866967298137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23681250915515911311532091 35521876373273866967298137)
      ·
        refine ⟨26641407279955400225473603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35521876373273866967298137 26641407279955400225473603)
        ·
          refine ⟨39962110919933100338210405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26641407279955400225473603 39962110919933100338210405)
          ·
            refine ⟨7492895797487456313414451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39962110919933100338210405 7492895797487456313414451)
            ·
              refine ⟨11239343696231184470121677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492895797487456313414451 11239343696231184470121677)
              ·
                refine ⟨4214753886086694176295629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11239343696231184470121677 4214753886086694176295629)
                ·
                  refine ⟨1580532707282510316110861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4214753886086694176295629 1580532707282510316110861)
                  ·
                    refine ⟨592699765230941368541573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580532707282510316110861 592699765230941368541573)
                    ·
                      rfl

theorem cell22_1731418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_1731418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731418 prefixEnd_1731418 := by exact prefixLift 1731418
  have htrace : WordTrace (prefixWord ++ tailWord_1731418) baseStart_1731418 baseEnd_1731418 := by
    simpa [prefixWord, tailWord_1731418, baseEnd_1731418] using wordTrace_append hprefix tailTrace_1731418
  have hstable : (prefixWord ++ tailWord_1731418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731418).length < 2 ^ (prefixWord ++ tailWord_1731418).sum := by decide
  have hdescent : baseEnd_1731418 < baseStart_1731418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731482 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_1731482 : Nat := 118140960795 + 1731482 * 2 ^ 59
def prefixEnd_1731482 : Nat := 4983230072969 + 3 ^ 40 * 1731482 * 2
def baseEnd_1731482 : Nat := 197573891246288844980459

theorem tailTrace_1731482 : CollatzResearch.WordTrace tailWord_1731482 prefixEnd_1731482 197573891246288844980459 := by
  unfold tailWord_1731482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788084178285975606937175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42101557808762601618499133 15788084178285975606937175)
  ·
    refine ⟨23682126267428963410405763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15788084178285975606937175 23682126267428963410405763)
    ·
      refine ⟨35523189401143445115608645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23682126267428963410405763 35523189401143445115608645)
      ·
        refine ⟨6660598012714395959176621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35523189401143445115608645 6660598012714395959176621)
        ·
          refine ⟨2497724254767898484691233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6660598012714395959176621 2497724254767898484691233)
          ·
            refine ⟨1873293191075923863518425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2497724254767898484691233 1873293191075923863518425)
            ·
              refine ⟨1404969893306942897638819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873293191075923863518425 1404969893306942897638819)
              ·
                refine ⟨2107454839960414346458229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404969893306942897638819 2107454839960414346458229)
                ·
                  refine ⟨197573891246288844980459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2107454839960414346458229 197573891246288844980459)
                  ·
                    rfl

theorem cell22_1731482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_1731482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731482 prefixEnd_1731482 := by exact prefixLift 1731482
  have htrace : WordTrace (prefixWord ++ tailWord_1731482) baseStart_1731482 baseEnd_1731482 := by
    simpa [prefixWord, tailWord_1731482, baseEnd_1731482] using wordTrace_append hprefix tailTrace_1731482
  have hstable : (prefixWord ++ tailWord_1731482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731482).length < 2 ^ (prefixWord ++ tailWord_1731482).sum := by decide
  have hdescent : baseEnd_1731482 < baseStart_1731482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731495 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1731495 : Nat := 118140960795 + 1731495 * 2 ^ 59
def prefixEnd_1731495 : Nat := 4983230072969 + 3 ^ 40 * 1731495 * 2
def baseEnd_1731495 : Nat := 592726123904538834366337

theorem tailTrace_1731495 : CollatzResearch.WordTrace tailWord_1731495 prefixEnd_1731495 592726123904538834366337 := by
  unfold tailWord_1731495
  simp only [CollatzResearch.WordTrace]
  refine ⟨63152810862096805647971939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42101873908064537098647959 63152810862096805647971939)
  ·
    refine ⟨94729216293145208471957909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63152810862096805647971939 94729216293145208471957909)
    ·
      refine ⟨4440432013741181647123027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94729216293145208471957909 4440432013741181647123027)
      ·
        refine ⟨6660648020611772470684541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440432013741181647123027 6660648020611772470684541)
        ·
          refine ⟨2497743007729414676506703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6660648020611772470684541 2497743007729414676506703)
          ·
            refine ⟨3746614511594122014760055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497743007729414676506703 3746614511594122014760055)
            ·
              refine ⟨5619921767391183022140083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746614511594122014760055 5619921767391183022140083)
              ·
                refine ⟨8429882651086774533210125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619921767391183022140083 8429882651086774533210125)
                ·
                  refine ⟨3161205994157540449953797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8429882651086774533210125 3161205994157540449953797)
                  ·
                    refine ⟨592726123904538834366337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3161205994157540449953797 592726123904538834366337)
                    ·
                      rfl

theorem cell22_1731495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1731495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731495 prefixEnd_1731495 := by exact prefixLift 1731495
  have htrace : WordTrace (prefixWord ++ tailWord_1731495) baseStart_1731495 baseEnd_1731495 := by
    simpa [prefixWord, tailWord_1731495, baseEnd_1731495] using wordTrace_append hprefix tailTrace_1731495
  have hstable : (prefixWord ++ tailWord_1731495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731495).length < 2 ^ (prefixWord ++ tailWord_1731495).sum := by decide
  have hdescent : baseEnd_1731495 < baseStart_1731495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731536 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_1731536 : Nat := 118140960795 + 1731536 * 2 ^ 59
def prefixEnd_1731536 : Nat := 4983230072969 + 3 ^ 40 * 1731536 * 2
def baseEnd_1731536 : Nat := 592740159042428394091211

theorem tailTrace_1731536 : CollatzResearch.WordTrace tailWord_1731536 prefixEnd_1731536 592740159042428394091211 := by
  unfold tailWord_1731536
  simp only [CollatzResearch.WordTrace]
  refine ⟨31577153127474134825107231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42102870836632179766809641 31577153127474134825107231)
  ·
    refine ⟨47365729691211202237660847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31577153127474134825107231 47365729691211202237660847)
    ·
      refine ⟨71048594536816803356491271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47365729691211202237660847 71048594536816803356491271)
      ·
        refine ⟨106572891805225205034736907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71048594536816803356491271 106572891805225205034736907)
        ·
          refine ⟨159859337707837807552105361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106572891805225205034736907 159859337707837807552105361)
          ·
            refine ⟨119894503280878355664079021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159859337707837807552105361 119894503280878355664079021)
            ·
              refine ⟨44960438730329383374029633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119894503280878355664079021 44960438730329383374029633)
              ·
                refine ⟨33720329047747037530522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44960438730329383374029633 33720329047747037530522225)
                ·
                  refine ⟨25290246785810278147891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33720329047747037530522225 25290246785810278147891669)
                  ·
                    refine ⟨592740159042428394091211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25290246785810278147891669 592740159042428394091211)
                    ·
                      rfl

theorem cell22_1731536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_1731536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731536 prefixEnd_1731536 := by exact prefixLift 1731536
  have htrace : WordTrace (prefixWord ++ tailWord_1731536) baseStart_1731536 baseEnd_1731536 := by
    simpa [prefixWord, tailWord_1731536, baseEnd_1731536] using wordTrace_append hprefix tailTrace_1731536
  have hstable : (prefixWord ++ tailWord_1731536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731536).length < 2 ^ (prefixWord ++ tailWord_1731536).sum := by decide
  have hdescent : baseEnd_1731536 < baseStart_1731536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731542 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1731542 : Nat := 118140960795 + 1731542 * 2 ^ 59
def prefixEnd_1731542 : Nat := 4983230072969 + 3 ^ 40 * 1731542 * 2
def baseEnd_1731542 : Nat := 592742212965046378441193

theorem tailTrace_1731542 : CollatzResearch.WordTrace tailWord_1731542 prefixEnd_1731542 592742212965046378441193 := by
  unfold tailWord_1731542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947157818307908292183305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42103016728617688449955253 3947157818307908292183305)
  ·
    refine ⟨2960368363730931219137479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3947157818307908292183305 2960368363730931219137479)
    ·
      refine ⟨4440552545596396828706219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960368363730931219137479 4440552545596396828706219)
      ·
        refine ⟨6660828818394595243059329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440552545596396828706219 6660828818394595243059329)
        ·
          refine ⟨4995621613795946432294497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6660828818394595243059329 4995621613795946432294497)
          ·
            refine ⟨3746716210346959824220873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4995621613795946432294497 3746716210346959824220873)
            ·
              refine ⟨2810037157760219868165655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746716210346959824220873 2810037157760219868165655)
              ·
                refine ⟨4215055736640329802248483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810037157760219868165655 4215055736640329802248483)
                ·
                  refine ⟨6322583604960494703372725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215055736640329802248483 6322583604960494703372725)
                  ·
                    refine ⟨592742212965046378441193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6322583604960494703372725 592742212965046378441193)
                    ·
                      rfl

theorem cell22_1731542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1731542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731542 prefixEnd_1731542 := by exact prefixLift 1731542
  have htrace : WordTrace (prefixWord ++ tailWord_1731542) baseStart_1731542 baseEnd_1731542 := by
    simpa [prefixWord, tailWord_1731542, baseEnd_1731542] using wordTrace_append hprefix tailTrace_1731542
  have hstable : (prefixWord ++ tailWord_1731542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731542).length < 2 ^ (prefixWord ++ tailWord_1731542).sum := by decide
  have hdescent : baseEnd_1731542 < baseStart_1731542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731645 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 6]
def baseStart_1731645 : Nat := 118140960795 + 1731645 * 2 ^ 59
def prefixEnd_1731645 : Nat := 4983230072969 + 3 ^ 40 * 1731645 * 2
def baseEnd_1731645 : Nat := 197592490656662814371959

theorem tailTrace_1731645 : CollatzResearch.WordTrace tailWord_1731645 prefixEnd_1731645 197592490656662814371959 := by
  unfold tailWord_1731645
  simp only [CollatzResearch.WordTrace]
  refine ⟨63158281811553381265932389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42105521207702254177288259 63158281811553381265932389)
  ·
    refine ⟨11842177839666258987362323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63158281811553381265932389 11842177839666258987362323)
    ·
      refine ⟨17763266759499388481043485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11842177839666258987362323 17763266759499388481043485)
      ·
        refine ⟨6661225034812270680391307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17763266759499388481043485 6661225034812270680391307)
        ·
          refine ⟨9991837552218406020586961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661225034812270680391307 9991837552218406020586961)
          ·
            refine ⟨7493878164163804515440221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9991837552218406020586961 7493878164163804515440221)
            ·
              refine ⟨2810204311561426693290083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7493878164163804515440221 2810204311561426693290083)
              ·
                refine ⟨4215306467342140039935125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810204311561426693290083 4215306467342140039935125)
                ·
                  refine ⟨197592490656662814371959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4215306467342140039935125 197592490656662814371959)
                  ·
                    rfl

theorem cell22_1731645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_1731645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731645 prefixEnd_1731645 := by exact prefixLift 1731645
  have htrace : WordTrace (prefixWord ++ tailWord_1731645) baseStart_1731645 baseEnd_1731645 := by
    simpa [prefixWord, tailWord_1731645, baseEnd_1731645] using wordTrace_append hprefix tailTrace_1731645
  have hstable : (prefixWord ++ tailWord_1731645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731645).length < 2 ^ (prefixWord ++ tailWord_1731645).sum := by decide
  have hdescent : baseEnd_1731645 < baseStart_1731645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731658 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1731658 : Nat := 118140960795 + 1731658 * 2 ^ 59
def prefixEnd_1731658 : Nat := 4983230072969 + 3 ^ 40 * 1731658 * 2
def baseEnd_1731658 : Nat := 592781922135660742540837

theorem tailTrace_1731658 : CollatzResearch.WordTrace tailWord_1731658 prefixEnd_1731658 592781922135660742540837 := by
  unfold tailWord_1731658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15789688990126571121538907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42105837307004189657437085 15789688990126571121538907)
  ·
    refine ⟨23684533485189856682308361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15789688990126571121538907 23684533485189856682308361)
    ·
      refine ⟨17763400113892392511731271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23684533485189856682308361 17763400113892392511731271)
      ·
        refine ⟨26645100170838588767596907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17763400113892392511731271 26645100170838588767596907)
        ·
          refine ⟨39967650256257883151395361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26645100170838588767596907 39967650256257883151395361)
          ·
            refine ⟨29975737692193412363546521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39967650256257883151395361 29975737692193412363546521)
            ·
              refine ⟨22481803269145059272659891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29975737692193412363546521 22481803269145059272659891)
              ·
                refine ⟨33722704903717588908989837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22481803269145059272659891 33722704903717588908989837)
                ·
                  refine ⟨12646014338894095840871189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33722704903717588908989837 12646014338894095840871189)
                  ·
                    refine ⟨592781922135660742540837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12646014338894095840871189 592781922135660742540837)
                    ·
                      rfl

theorem cell22_1731658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1731658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731658 prefixEnd_1731658 := by exact prefixLift 1731658
  have htrace : WordTrace (prefixWord ++ tailWord_1731658) baseStart_1731658 baseEnd_1731658 := by
    simpa [prefixWord, tailWord_1731658, baseEnd_1731658] using wordTrace_append hprefix tailTrace_1731658
  have hstable : (prefixWord ++ tailWord_1731658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731658).length < 2 ^ (prefixWord ++ tailWord_1731658).sum := by decide
  have hdescent : baseEnd_1731658 < baseStart_1731658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731694 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1731694 : Nat := 118140960795 + 1731694 * 2 ^ 59
def prefixEnd_1731694 : Nat := 4983230072969 + 3 ^ 40 * 1731694 * 2
def baseEnd_1731694 : Nat := 592794245671368648640727

theorem tailTrace_1731694 : CollatzResearch.WordTrace tailWord_1731694 prefixEnd_1731694 592794245671368648640727 := by
  unfold tailWord_1731694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895008623546982829308267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42106712658917241756310757 7895008623546982829308267)
  ·
    refine ⟨11842512935320474243962401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7895008623546982829308267 11842512935320474243962401)
    ·
      refine ⟨8881884701490355682971801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11842512935320474243962401 8881884701490355682971801)
      ·
        refine ⟨6661413526117766762228851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8881884701490355682971801 6661413526117766762228851)
        ·
          refine ⟨9992120289176650143343277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661413526117766762228851 9992120289176650143343277)
          ·
            refine ⟨3747045108441243803753729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9992120289176650143343277 3747045108441243803753729)
            ·
              refine ⟨2810283831330932852815297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3747045108441243803753729 2810283831330932852815297)
              ·
                refine ⟨2107712873498199639611473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810283831330932852815297 2107712873498199639611473)
                ·
                  refine ⟨1580784655123649729708605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2107712873498199639611473 1580784655123649729708605)
                  ·
                    refine ⟨592794245671368648640727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580784655123649729708605 592794245671368648640727)
                    ·
                      rfl

theorem cell22_1731694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1731694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731694 prefixEnd_1731694 := by exact prefixLift 1731694
  have htrace : WordTrace (prefixWord ++ tailWord_1731694) baseStart_1731694 baseEnd_1731694 := by
    simpa [prefixWord, tailWord_1731694, baseEnd_1731694] using wordTrace_append hprefix tailTrace_1731694
  have hstable : (prefixWord ++ tailWord_1731694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731694).length < 2 ^ (prefixWord ++ tailWord_1731694).sum := by decide
  have hdescent : baseEnd_1731694 < baseStart_1731694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731703 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1731703 : Nat := 118140960795 + 1731703 * 2 ^ 59
def prefixEnd_1731703 : Nat := 4983230072969 + 3 ^ 40 * 1731703 * 2
def baseEnd_1731703 : Nat := 592797326555295625165699

theorem tailTrace_1731703 : CollatzResearch.WordTrace tailWord_1731703 prefixEnd_1731703 592797326555295625165699 := by
  unfold tailWord_1731703
  simp only [CollatzResearch.WordTrace]
  refine ⟨63160397245343257171543763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42106931496895504781029175 63160397245343257171543763)
  ·
    refine ⟨94740595868014885757315645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63160397245343257171543763 94740595868014885757315645)
    ·
      refine ⟨35527723450505582158993367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94740595868014885757315645 35527723450505582158993367)
      ·
        refine ⟨53291585175758373238490051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35527723450505582158993367 53291585175758373238490051)
        ·
          refine ⟨79937377763637559857735077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53291585175758373238490051 79937377763637559857735077)
          ·
            refine ⟨14988258330682042473325327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79937377763637559857735077 14988258330682042473325327)
            ·
              refine ⟨22482387496023063709987991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14988258330682042473325327 22482387496023063709987991)
              ·
                refine ⟨33723581244034595564981987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22482387496023063709987991 33723581244034595564981987)
                ·
                  refine ⟨50585371866051893347472981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33723581244034595564981987 50585371866051893347472981)
                  ·
                    refine ⟨592797326555295625165699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50585371866051893347472981 592797326555295625165699)
                    ·
                      rfl

theorem cell22_1731703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1731703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731703 prefixEnd_1731703 := by exact prefixLift 1731703
  have htrace : WordTrace (prefixWord ++ tailWord_1731703) baseStart_1731703 baseEnd_1731703 := by
    simpa [prefixWord, tailWord_1731703, baseEnd_1731703] using wordTrace_append hprefix tailTrace_1731703
  have hstable : (prefixWord ++ tailWord_1731703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731703).length < 2 ^ (prefixWord ++ tailWord_1731703).sum := by decide
  have hdescent : baseEnd_1731703 < baseStart_1731703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731722 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_1731722 : Nat := 118140960795 + 1731722 * 2 ^ 59
def prefixEnd_1731722 : Nat := 4983230072969 + 3 ^ 40 * 1731722 * 2
def baseEnd_1731722 : Nat := 592803830643585908940641

theorem tailTrace_1731722 : CollatzResearch.WordTrace tailWord_1731722 prefixEnd_1731722 592803830643585908940641 := by
  unfold tailWord_1731722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15790272558068605854121355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42107393488182948944323613 15790272558068605854121355)
  ·
    refine ⟨23685408837102908781182033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15790272558068605854121355 23685408837102908781182033)
    ·
      refine ⟨17764056627827181585886525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23685408837102908781182033 17764056627827181585886525)
      ·
        refine ⟨6661521235435193094707447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17764056627827181585886525 6661521235435193094707447)
        ·
          refine ⟨9992281853152789642061171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661521235435193094707447 9992281853152789642061171)
          ·
            refine ⟨14988422779729184463091757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9992281853152789642061171 14988422779729184463091757)
            ·
              refine ⟨5620658542398444173659409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14988422779729184463091757 5620658542398444173659409)
              ·
                refine ⟨4215493906798833130244557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620658542398444173659409 4215493906798833130244557)
                ·
                  refine ⟨1580810215049562423841709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4215493906798833130244557 1580810215049562423841709)
                  ·
                    refine ⟨592803830643585908940641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580810215049562423841709 592803830643585908940641)
                    ·
                      rfl

theorem cell22_1731722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_1731722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731722 prefixEnd_1731722 := by exact prefixLift 1731722
  have htrace : WordTrace (prefixWord ++ tailWord_1731722) baseStart_1731722 baseEnd_1731722 := by
    simpa [prefixWord, tailWord_1731722, baseEnd_1731722] using wordTrace_append hprefix tailTrace_1731722
  have hstable : (prefixWord ++ tailWord_1731722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731722).length < 2 ^ (prefixWord ++ tailWord_1731722).sum := by decide
  have hdescent : baseEnd_1731722 < baseStart_1731722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731812 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1731812 : Nat := 118140960795 + 1731812 * 2 ^ 59
def prefixEnd_1731812 : Nat := 4983230072969 + 3 ^ 40 * 1731812 * 2
def baseEnd_1731812 : Nat := 592834639482855674190365

theorem tailTrace_1731812 : CollatzResearch.WordTrace tailWord_1731812 prefixEnd_1731812 592834639482855674190365 := by
  unfold tailWord_1731812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31582186400974184393630845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42109581867965579191507793 31582186400974184393630845)
  ·
    refine ⟨11843319900365319147611567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31582186400974184393630845 11843319900365319147611567)
    ·
      refine ⟨17764979850547978721417351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11843319900365319147611567 17764979850547978721417351)
      ·
        refine ⟨26647469775821968082126027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17764979850547978721417351 26647469775821968082126027)
        ·
          refine ⟨39971204663732952123189041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26647469775821968082126027 39971204663732952123189041)
          ·
            refine ⟨29978403497799714092391781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39971204663732952123189041 29978403497799714092391781)
            ·
              refine ⟨5620950655837446392323459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29978403497799714092391781 5620950655837446392323459)
              ·
                refine ⟨8431425983756169588485189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620950655837446392323459 8431425983756169588485189)
                ·
                  refine ⟨1580892371954281797840973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8431425983756169588485189 1580892371954281797840973)
                  ·
                    refine ⟨592834639482855674190365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580892371954281797840973 592834639482855674190365)
                    ·
                      rfl

theorem cell22_1731812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1731812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731812 prefixEnd_1731812 := by exact prefixLift 1731812
  have htrace : WordTrace (prefixWord ++ tailWord_1731812) baseStart_1731812 baseEnd_1731812 := by
    simpa [prefixWord, tailWord_1731812, baseEnd_1731812] using wordTrace_append hprefix tailTrace_1731812
  have hstable : (prefixWord ++ tailWord_1731812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731812).length < 2 ^ (prefixWord ++ tailWord_1731812).sum := by decide
  have hdescent : baseEnd_1731812 < baseStart_1731812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731844 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1731844 : Nat := 118140960795 + 1731844 * 2 ^ 59
def prefixEnd_1731844 : Nat := 4983230072969 + 3 ^ 40 * 1731844 * 2
def baseEnd_1731844 : Nat := 592845593736818257390267

theorem tailTrace_1731844 : CollatzResearch.WordTrace tailWord_1731844 prefixEnd_1731844 592845593736818257390267 := by
  unfold tailWord_1731844
  simp only [CollatzResearch.WordTrace]
  refine ⟨31582769968916219126213293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42110359958554958834951057 31582769968916219126213293)
  ·
    refine ⟨11843538738343582172329985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31582769968916219126213293 11843538738343582172329985)
    ·
      refine ⟨8882654053757686629247489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11843538738343582172329985 8882654053757686629247489)
      ·
        refine ⟨6661990540318264971935617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8882654053757686629247489 6661990540318264971935617)
        ·
          refine ⟨4996492905238698728951713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6661990540318264971935617 4996492905238698728951713)
          ·
            refine ⟨3747369678929024046713785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4996492905238698728951713 3747369678929024046713785)
            ·
              refine ⟨2810527259196768035035339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3747369678929024046713785 2810527259196768035035339)
              ·
                refine ⟨4215790888795152052553009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810527259196768035035339 4215790888795152052553009)
                ·
                  refine ⟨3161843166596364039414757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4215790888795152052553009 3161843166596364039414757)
                  ·
                    refine ⟨592845593736818257390267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3161843166596364039414757 592845593736818257390267)
                    ·
                      rfl

theorem cell22_1731844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1731844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731844 prefixEnd_1731844 := by exact prefixLift 1731844
  have htrace : WordTrace (prefixWord ++ tailWord_1731844) baseStart_1731844 baseEnd_1731844 := by
    simpa [prefixWord, tailWord_1731844, baseEnd_1731844] using wordTrace_append hprefix tailTrace_1731844
  have hstable : (prefixWord ++ tailWord_1731844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731844).length < 2 ^ (prefixWord ++ tailWord_1731844).sum := by decide
  have hdescent : baseEnd_1731844 < baseStart_1731844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731902 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1731902 : Nat := 118140960795 + 1731902 * 2 ^ 59
def prefixEnd_1731902 : Nat := 4983230072969 + 3 ^ 40 * 1731902 * 2
def baseEnd_1731902 : Nat := 592865448322125439440089

theorem tailTrace_1731902 : CollatzResearch.WordTrace tailWord_1731902 prefixEnd_1731902 592865448322125439440089 := by
  unfold tailWord_1731902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895956921452789269754745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42111770247748209438691973 7895956921452789269754745)
  ·
    refine ⟨5921967691089591952316059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7895956921452789269754745 5921967691089591952316059)
    ·
      refine ⟨8882951536634387928474089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5921967691089591952316059 8882951536634387928474089)
      ·
        refine ⟨6662213652475790946355567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8882951536634387928474089 6662213652475790946355567)
        ·
          refine ⟨9993320478713686419533351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662213652475790946355567 9993320478713686419533351)
          ·
            refine ⟨14989980718070529629300027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993320478713686419533351 14989980718070529629300027)
            ·
              refine ⟨22484971077105794443950041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14989980718070529629300027 22484971077105794443950041)
              ·
                refine ⟨16863728307829345832962531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22484971077105794443950041 16863728307829345832962531)
                ·
                  refine ⟨25295592461744018749443797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16863728307829345832962531 25295592461744018749443797)
                  ·
                    refine ⟨592865448322125439440089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25295592461744018749443797 592865448322125439440089)
                    ·
                      rfl

theorem cell22_1731902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1731902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731902 prefixEnd_1731902 := by exact prefixLift 1731902
  have htrace : WordTrace (prefixWord ++ tailWord_1731902) baseStart_1731902 baseEnd_1731902 := by
    simpa [prefixWord, tailWord_1731902, baseEnd_1731902] using wordTrace_append hprefix tailTrace_1731902
  have hstable : (prefixWord ++ tailWord_1731902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731902).length < 2 ^ (prefixWord ++ tailWord_1731902).sum := by decide
  have hdescent : baseEnd_1731902 < baseStart_1731902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731908 : List Nat := [2, 3, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1731908 : Nat := 118140960795 + 1731908 * 2 ^ 59
def prefixEnd_1731908 : Nat := 4983230072969 + 3 ^ 40 * 1731908 * 2
def baseEnd_1731908 : Nat := 592867502244743423790071

theorem tailTrace_1731908 : CollatzResearch.WordTrace tailWord_1731908 prefixEnd_1731908 592867502244743423790071 := by
  unfold tailWord_1731908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31583937104800288591378189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42111916139733718121837585 31583937104800288591378189)
  ·
    refine ⟨11843976414300108221766821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31583937104800288591378189 11843976414300108221766821)
    ·
      refine ⟨2220745577681270291581279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11843976414300108221766821 2220745577681270291581279)
      ·
        refine ⟨3331118366521905437371919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220745577681270291581279 3331118366521905437371919)
        ·
          refine ⟨4996677549782858156057879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331118366521905437371919 4996677549782858156057879)
          ·
            refine ⟨7495016324674287234086819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996677549782858156057879 7495016324674287234086819)
            ·
              refine ⟨11242524487011430851130229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495016324674287234086819 11242524487011430851130229)
              ·
                refine ⟨1053986670657321642293459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11242524487011430851130229 1053986670657321642293459)
                ·
                  refine ⟨1580980005985982463440189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053986670657321642293459 1580980005985982463440189)
                  ·
                    refine ⟨592867502244743423790071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1580980005985982463440189 592867502244743423790071)
                    ·
                      rfl

theorem cell22_1731908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1731908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731908 prefixEnd_1731908 := by exact prefixLift 1731908
  have htrace : WordTrace (prefixWord ++ tailWord_1731908) baseStart_1731908 baseEnd_1731908 := by
    simpa [prefixWord, tailWord_1731908, baseEnd_1731908] using wordTrace_append hprefix tailTrace_1731908
  have hstable : (prefixWord ++ tailWord_1731908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731908).length < 2 ^ (prefixWord ++ tailWord_1731908).sum := by decide
  have hdescent : baseEnd_1731908 < baseStart_1731908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731947 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 8, 3]
def baseStart_1731947 : Nat := 118140960795 + 1731947 * 2 ^ 59
def prefixEnd_1731947 : Nat := 4983230072969 + 3 ^ 40 * 1731947 * 2
def baseEnd_1731947 : Nat := 592880852741760322064951

theorem tailTrace_1731947 : CollatzResearch.WordTrace tailWord_1731947 prefixEnd_1731947 592880852741760322064951 := by
  unfold tailWord_1731947
  simp only [CollatzResearch.WordTrace]
  refine ⟨63169296656459286843426095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42112864437639524562284063 63169296656459286843426095)
  ·
    refine ⟨94753944984688930265139143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63169296656459286843426095 94753944984688930265139143)
    ·
      refine ⟨142130917477033395397708715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94753944984688930265139143 142130917477033395397708715)
      ·
        refine ⟨213196376215550093096563073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142130917477033395397708715 213196376215550093096563073)
        ·
          refine ⟨159897282161662569822422305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213196376215550093096563073 159897282161662569822422305)
          ·
            refine ⟨119922961621246927366816729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159897282161662569822422305 119922961621246927366816729)
            ·
              refine ⟨89942221215935195525112547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119922961621246927366816729 89942221215935195525112547)
              ·
                refine ⟨134913331823902793287668821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89942221215935195525112547 134913331823902793287668821)
                ·
                  refine ⟨1581015607311360858839869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 134913331823902793287668821 1581015607311360858839869)
                  ·
                    refine ⟨592880852741760322064951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581015607311360858839869 592880852741760322064951)
                    ·
                      rfl

theorem cell22_1731947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 3].length) (baseStart_1731947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1731947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1731947 prefixEnd_1731947 := by exact prefixLift 1731947
  have htrace : WordTrace (prefixWord ++ tailWord_1731947) baseStart_1731947 baseEnd_1731947 := by
    simpa [prefixWord, tailWord_1731947, baseEnd_1731947] using wordTrace_append hprefix tailTrace_1731947
  have hstable : (prefixWord ++ tailWord_1731947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731947).length < 2 ^ (prefixWord ++ tailWord_1731947).sum := by decide
  have hdescent : baseEnd_1731947 < baseStart_1731947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732039 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 5]
def baseStart_1732039 : Nat := 118140960795 + 1732039 * 2 ^ 59
def prefixEnd_1732039 : Nat := 4983230072969 + 3 ^ 40 * 1732039 * 2
def baseEnd_1732039 : Nat := 197637448740634249588223

theorem tailTrace_1732039 : CollatzResearch.WordTrace tailWord_1732039 prefixEnd_1732039 197637448740634249588223 := by
  unfold tailWord_1732039
  simp only [CollatzResearch.WordTrace]
  refine ⟨63172652172125986555775171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42115101448083991037183447 63172652172125986555775171)
  ·
    refine ⟨94758978258188979833662757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63172652172125986555775171 94758978258188979833662757)
    ·
      refine ⟨17767308423410433718811767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94758978258188979833662757 17767308423410433718811767)
      ·
        refine ⟨26650962635115650578217651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17767308423410433718811767 26650962635115650578217651)
        ·
          refine ⟨39976443952673475867326477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26650962635115650578217651 39976443952673475867326477)
          ·
            refine ⟨14991166482252553450247429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39976443952673475867326477 14991166482252553450247429)
            ·
              refine ⟨2810843715422353771921393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14991166482252553450247429 2810843715422353771921393)
              ·
                refine ⟨2108132786566765328941045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810843715422353771921393 2108132786566765328941045)
                ·
                  refine ⟨197637448740634249588223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2108132786566765328941045 197637448740634249588223)
                  ·
                    rfl

theorem cell22_1732039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 5].length) (baseStart_1732039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732039 prefixEnd_1732039 := by exact prefixLift 1732039
  have htrace : WordTrace (prefixWord ++ tailWord_1732039) baseStart_1732039 baseEnd_1732039 := by
    simpa [prefixWord, tailWord_1732039, baseEnd_1732039] using wordTrace_append hprefix tailTrace_1732039
  have hstable : (prefixWord ++ tailWord_1732039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732039).length < 2 ^ (prefixWord ++ tailWord_1732039).sum := by decide
  have hdescent : baseEnd_1732039 < baseStart_1732039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732043 : List Nat := [1, 1, 1, 1, 3, 3, 6, 2, 1, 3]
def baseStart_1732043 : Nat := 118140960795 + 1732043 * 2 ^ 59
def prefixEnd_1732043 : Nat := 4983230072969 + 3 ^ 40 * 1732043 * 2
def baseEnd_1732043 : Nat := 592913715503648071664657

theorem tailTrace_1732043 : CollatzResearch.WordTrace tailWord_1732043 prefixEnd_1732043 592913715503648071664657 := by
  unfold tailWord_1732043
  simp only [CollatzResearch.WordTrace]
  refine ⟨63172798064111495238920783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42115198709407663492613855 63172798064111495238920783)
  ·
    refine ⟨94759197096167242858381175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63172798064111495238920783 94759197096167242858381175)
    ·
      refine ⟨142138795644250864287571763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94759197096167242858381175 142138795644250864287571763)
      ·
        refine ⟨213208193466376296431357645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142138795644250864287571763 213208193466376296431357645)
        ·
          refine ⟨79953072549891111161759117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213208193466376296431357645 79953072549891111161759117)
          ·
            refine ⟨29982402206209166685659669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79953072549891111161759117 29982402206209166685659669)
            ·
              refine ⟨1405425103416054688390297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29982402206209166685659669 1405425103416054688390297)
              ·
                refine ⟨1054068827562041016292723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405425103416054688390297 1054068827562041016292723)
                ·
                  refine ⟨1581103241343061524439085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054068827562041016292723 1581103241343061524439085)
                  ·
                    refine ⟨592913715503648071664657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581103241343061524439085 592913715503648071664657)
                    ·
                      rfl

theorem cell22_1732043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 3].length) (baseStart_1732043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732043 prefixEnd_1732043 := by exact prefixLift 1732043
  have htrace : WordTrace (prefixWord ++ tailWord_1732043) baseStart_1732043 baseEnd_1732043 := by
    simpa [prefixWord, tailWord_1732043, baseEnd_1732043] using wordTrace_append hprefix tailTrace_1732043
  have hstable : (prefixWord ++ tailWord_1732043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732043).length < 2 ^ (prefixWord ++ tailWord_1732043).sum := by decide
  have hdescent : baseEnd_1732043 < baseStart_1732043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732129 : List Nat := [1, 2, 3, 2, 2, 3, 1, 8]
def baseStart_1732129 : Nat := 118140960795 + 1732129 * 2 ^ 59
def prefixEnd_1732129 : Nat := 4983230072969 + 3 ^ 40 * 1732129 * 2
def baseEnd_1732129 : Nat := 65882572784574723779377

theorem tailTrace_1732129 : CollatzResearch.WordTrace tailWord_1732129 prefixEnd_1732129 65882572784574723779377 := by
  unfold tailWord_1732129
  simp only [CollatzResearch.WordTrace]
  refine ⟨63175934741799931926551441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42117289827866621284367627 63175934741799931926551441)
  ·
    refine ⟨47381951056349948944913581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63175934741799931926551441 47381951056349948944913581)
    ·
      refine ⟨17768231646131230854342593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47381951056349948944913581 17768231646131230854342593)
      ·
        refine ⟨13326173734598423140756945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17768231646131230854342593 13326173734598423140756945)
        ·
          refine ⟨9994630300948817355567709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13326173734598423140756945 9994630300948817355567709)
          ·
            refine ⟨3747986362855806508337891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9994630300948817355567709 3747986362855806508337891)
            ·
              refine ⟨5621979544283709762506837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747986362855806508337891 5621979544283709762506837)
              ·
                refine ⟨65882572784574723779377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5621979544283709762506837 65882572784574723779377)
                ·
                  rfl

theorem cell22_1732129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 8].length) (baseStart_1732129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732129 prefixEnd_1732129 := by exact prefixLift 1732129
  have htrace : WordTrace (prefixWord ++ tailWord_1732129) baseStart_1732129 baseEnd_1732129 := by
    simpa [prefixWord, tailWord_1732129, baseEnd_1732129] using wordTrace_append hprefix tailTrace_1732129
  have hstable : (prefixWord ++ tailWord_1732129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732129).length < 2 ^ (prefixWord ++ tailWord_1732129).sum := by decide
  have hdescent : baseEnd_1732129 < baseStart_1732129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732167 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 2, 3]
def baseStart_1732167 : Nat := 118140960795 + 1732167 * 2 ^ 59
def prefixEnd_1732167 : Nat := 4983230072969 + 3 ^ 40 * 1732167 * 2
def baseEnd_1732167 : Nat := 592956163237753081564277

theorem tailTrace_1732167 : CollatzResearch.WordTrace tailWord_1732167 prefixEnd_1732167 592956163237753081564277 := by
  unfold tailWord_1732167
  simp only [CollatzResearch.WordTrace]
  refine ⟨63177320715662264416434755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42118213810441509610956503 63177320715662264416434755)
  ·
    refine ⟨94765981073493396624652133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63177320715662264416434755 94765981073493396624652133)
    ·
      refine ⟨17768621451280011867122275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94765981073493396624652133 17768621451280011867122275)
      ·
        refine ⟨26652932176920017800683413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768621451280011867122275 26652932176920017800683413)
        ·
          refine ⟨1249356195793125834407035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26652932176920017800683413 1249356195793125834407035)
          ·
            refine ⟨1874034293689688751610553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249356195793125834407035 1874034293689688751610553)
            ·
              refine ⟨1405525720267266563707915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874034293689688751610553 1405525720267266563707915)
              ·
                refine ⟨2108288580400899845561873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405525720267266563707915 2108288580400899845561873)
                ·
                  refine ⟨1581216435300674884171405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108288580400899845561873 1581216435300674884171405)
                  ·
                    refine ⟨592956163237753081564277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581216435300674884171405 592956163237753081564277)
                    ·
                      rfl

theorem cell22_1732167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_1732167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732167 prefixEnd_1732167 := by exact prefixLift 1732167
  have htrace : WordTrace (prefixWord ++ tailWord_1732167) baseStart_1732167 baseEnd_1732167 := by
    simpa [prefixWord, tailWord_1732167, baseEnd_1732167] using wordTrace_append hprefix tailTrace_1732167
  have hstable : (prefixWord ++ tailWord_1732167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732167).length < 2 ^ (prefixWord ++ tailWord_1732167).sum := by decide
  have hdescent : baseEnd_1732167 < baseStart_1732167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732182 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1732182 : Nat := 118140960795 + 1732182 * 2 ^ 59
def prefixEnd_1732182 : Nat := 4983230072969 + 3 ^ 40 * 1732182 * 2
def baseEnd_1732182 : Nat := 592961298044298042439231

theorem tailTrace_1732182 : CollatzResearch.WordTrace tailWord_1732182 prefixEnd_1732182 592961298044298042439231 := by
  unfold tailWord_1732182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948616738162995123639425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42118578540405281318820533 3948616738162995123639425)
  ·
    refine ⟨2961462553622246342729569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3948616738162995123639425 2961462553622246342729569)
    ·
      refine ⟨2221096915216684757047177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2961462553622246342729569 2221096915216684757047177)
      ·
        refine ⟨1665822686412513567785383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2221096915216684757047177 1665822686412513567785383)
        ·
          refine ⟨2498734029618770351678075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665822686412513567785383 2498734029618770351678075)
          ·
            refine ⟨3748101044428155527517113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498734029618770351678075 3748101044428155527517113)
            ·
              refine ⟨2811075783321116645637835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3748101044428155527517113 2811075783321116645637835)
              ·
                refine ⟨4216613674981674968456753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811075783321116645637835 4216613674981674968456753)
                ·
                  refine ⟨3162460256236256226342565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216613674981674968456753 3162460256236256226342565)
                  ·
                    refine ⟨592961298044298042439231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3162460256236256226342565 592961298044298042439231)
                    ·
                      rfl

theorem cell22_1732182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1732182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732182 prefixEnd_1732182 := by exact prefixLift 1732182
  have htrace : WordTrace (prefixWord ++ tailWord_1732182) baseStart_1732182 baseEnd_1732182 := by
    simpa [prefixWord, tailWord_1732182, baseEnd_1732182] using wordTrace_append hprefix tailTrace_1732182
  have hstable : (prefixWord ++ tailWord_1732182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732182).length < 2 ^ (prefixWord ++ tailWord_1732182).sum := by decide
  have hdescent : baseEnd_1732182 < baseStart_1732182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732219 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 6]
def baseStart_1732219 : Nat := 118140960795 + 1732219 * 2 ^ 59
def prefixEnd_1732219 : Nat := 4983230072969 + 3 ^ 40 * 1732219 * 2
def baseEnd_1732219 : Nat := 197657987966814093088039

theorem tailTrace_1732219 : CollatzResearch.WordTrace tailWord_1732219 prefixEnd_1732219 197657987966814093088039 := by
  unfold tailWord_1732219
  simp only [CollatzResearch.WordTrace]
  refine ⟨63179217311473877297327711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42119478207649251531551807 63179217311473877297327711)
  ·
    refine ⟨94768825967210815945991567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63179217311473877297327711 94768825967210815945991567)
    ·
      refine ⟨142153238950816223918987351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94768825967210815945991567 142153238950816223918987351)
      ·
        refine ⟨213229858426224335878481027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142153238950816223918987351 213229858426224335878481027)
        ·
          refine ⟨319844787639336503817721541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213229858426224335878481027 319844787639336503817721541)
          ·
            refine ⟨59970897682375594465822789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319844787639336503817721541 59970897682375594465822789)
            ·
              refine ⟨11244543315445423962341773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59970897682375594465822789 11244543315445423962341773)
              ·
                refine ⟨4216703743292033985878165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11244543315445423962341773 4216703743292033985878165)
                ·
                  refine ⟨197657987966814093088039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4216703743292033985878165 197657987966814093088039)
                  ·
                    rfl

theorem cell22_1732219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 6].length) (baseStart_1732219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732219 prefixEnd_1732219 := by exact prefixLift 1732219
  have htrace : WordTrace (prefixWord ++ tailWord_1732219) baseStart_1732219 baseEnd_1732219 := by
    simpa [prefixWord, tailWord_1732219, baseEnd_1732219] using wordTrace_append hprefix tailTrace_1732219
  have hstable : (prefixWord ++ tailWord_1732219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732219).length < 2 ^ (prefixWord ++ tailWord_1732219).sum := by decide
  have hdescent : baseEnd_1732219 < baseStart_1732219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732221 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1732221 : Nat := 118140960795 + 1732221 * 2 ^ 59
def prefixEnd_1732221 : Nat := 4983230072969 + 3 ^ 40 * 1732221 * 2
def baseEnd_1732221 : Nat := 592974648541314940714111

theorem tailTrace_1732221 : CollatzResearch.WordTrace tailWord_1732221 prefixEnd_1732221 592974648541314940714111 := by
  unfold tailWord_1732221
  simp only [CollatzResearch.WordTrace]
  refine ⟨63179290257466631638900517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42119526838311087759267011 63179290257466631638900517)
  ·
    refine ⟨11846116923274993432293847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63179290257466631638900517 11846116923274993432293847)
    ·
      refine ⟨17769175384912490148440771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11846116923274993432293847 17769175384912490148440771)
      ·
        refine ⟨26653763077368735222661157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17769175384912490148440771 26653763077368735222661157)
        ·
          refine ⟨4997580577006637854248967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26653763077368735222661157 4997580577006637854248967)
          ·
            refine ⟨7496370865509956781373451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997580577006637854248967 7496370865509956781373451)
            ·
              refine ⟨11244556298264935172060177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496370865509956781373451 11244556298264935172060177)
              ·
                refine ⟨8433417223698701379045133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11244556298264935172060177 8433417223698701379045133)
                ·
                  refine ⟨3162531458887013017141925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8433417223698701379045133 3162531458887013017141925)
                  ·
                    refine ⟨592974648541314940714111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3162531458887013017141925 592974648541314940714111)
                    ·
                      rfl

theorem cell22_1732221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1732221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732221 prefixEnd_1732221 := by exact prefixLift 1732221
  have htrace : WordTrace (prefixWord ++ tailWord_1732221) baseStart_1732221 baseEnd_1732221 := by
    simpa [prefixWord, tailWord_1732221, baseEnd_1732221] using wordTrace_append hprefix tailTrace_1732221
  have hstable : (prefixWord ++ tailWord_1732221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732221).length < 2 ^ (prefixWord ++ tailWord_1732221).sum := by decide
  have hdescent : baseEnd_1732221 < baseStart_1732221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732255 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 1, 4]
def baseStart_1732255 : Nat := 118140960795 + 1732255 * 2 ^ 59
def prefixEnd_1732255 : Nat := 4983230072969 + 3 ^ 40 * 1732255 * 2
def baseEnd_1732255 : Nat := 592986287436150185364007

theorem tailTrace_1732255 : CollatzResearch.WordTrace tailWord_1732255 prefixEnd_1732255 592986287436150185364007 := by
  unfold tailWord_1732255
  simp only [CollatzResearch.WordTrace]
  refine ⟨63180530339343455445638219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42120353559562303630425479 63180530339343455445638219)
  ·
    refine ⟨94770795509015183168457329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63180530339343455445638219 94770795509015183168457329)
    ·
      refine ⟨71078096631761387376342997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94770795509015183168457329 71078096631761387376342997)
      ·
        refine ⟨1665892889806907516633039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 71078096631761387376342997 1665892889806907516633039)
        ·
          refine ⟨2498839334710361274949559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665892889806907516633039 2498839334710361274949559)
          ·
            refine ⟨3748259002065541912424339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498839334710361274949559 3748259002065541912424339)
            ·
              refine ⟨5622388503098312868636509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748259002065541912424339 5622388503098312868636509)
              ·
                refine ⟨2108395688661867325738691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5622388503098312868636509 2108395688661867325738691)
                ·
                  refine ⟨3162593532992800988608037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108395688661867325738691 3162593532992800988608037)
                  ·
                    refine ⟨592986287436150185364007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3162593532992800988608037 592986287436150185364007)
                    ·
                      rfl

theorem cell22_1732255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_1732255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732255 prefixEnd_1732255 := by exact prefixLift 1732255
  have htrace : WordTrace (prefixWord ++ tailWord_1732255) baseStart_1732255 baseEnd_1732255 := by
    simpa [prefixWord, tailWord_1732255, baseEnd_1732255] using wordTrace_append hprefix tailTrace_1732255
  have hstable : (prefixWord ++ tailWord_1732255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732255).length < 2 ^ (prefixWord ++ tailWord_1732255).sum := by decide
  have hdescent : baseEnd_1732255 < baseStart_1732255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732270 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1732270 : Nat := 118140960795 + 1732270 * 2 ^ 59
def prefixEnd_1732270 : Nat := 4983230072969 + 3 ^ 40 * 1732270 * 2
def baseEnd_1732270 : Nat := 197663807414231715412987

theorem tailTrace_1732270 : CollatzResearch.WordTrace tailWord_1732270 prefixEnd_1732270 197663807414231715412987 := by
  unfold tailWord_1732270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7897634679286139125929283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42120718289526075338289509 7897634679286139125929283)
  ·
    refine ⟨11846452018929208688893925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7897634679286139125929283 11846452018929208688893925)
    ·
      refine ⟨2221209753549226629167611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11846452018929208688893925 2221209753549226629167611)
      ·
        refine ⟨3331814630323839943751417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221209753549226629167611 3331814630323839943751417)
        ·
          refine ⟨2498860972742879957813563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331814630323839943751417 2498860972742879957813563)
          ·
            refine ⟨3748291459114319936720345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498860972742879957813563 3748291459114319936720345)
            ·
              refine ⟨2811218594335739952540259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3748291459114319936720345 2811218594335739952540259)
              ·
                refine ⟨4216827891503609928810389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811218594335739952540259 4216827891503609928810389)
                ·
                  refine ⟨197663807414231715412987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4216827891503609928810389 197663807414231715412987)
                  ·
                    rfl

theorem cell22_1732270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1732270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732270 prefixEnd_1732270 := by exact prefixLift 1732270
  have htrace : WordTrace (prefixWord ++ tailWord_1732270) baseStart_1732270 baseEnd_1732270 := by
    simpa [prefixWord, tailWord_1732270, baseEnd_1732270] using wordTrace_append hprefix tailTrace_1732270
  have hstable : (prefixWord ++ tailWord_1732270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732270).length < 2 ^ (prefixWord ++ tailWord_1732270).sum := by decide
  have hdescent : baseEnd_1732270 < baseStart_1732270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732285 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_1732285 : Nat := 118140960795 + 1732285 * 2 ^ 59
def prefixEnd_1732285 : Nat := 4983230072969 + 3 ^ 40 * 1732285 * 2
def baseEnd_1732285 : Nat := 592996557049240107113915

theorem tailTrace_1732285 : CollatzResearch.WordTrace tailWord_1732285 prefixEnd_1732285 592996557049240107113915 := by
  unfold tailWord_1732285
  simp only [CollatzResearch.WordTrace]
  refine ⟨63181624529234770569230309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42121083019489847046153539 63181624529234770569230309)
  ·
    refine ⟨11846554599231519481730683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63181624529234770569230309 11846554599231519481730683)
    ·
      refine ⟨17769831898847279222596025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11846554599231519481730683 17769831898847279222596025)
      ·
        refine ⟨13327373924135459416947019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17769831898847279222596025 13327373924135459416947019)
        ·
          refine ⟨19991060886203189125420529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13327373924135459416947019 19991060886203189125420529)
          ·
            refine ⟨14993295664652391844065397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19991060886203189125420529 14993295664652391844065397)
            ·
              refine ⟨1405621468561161735381131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14993295664652391844065397 1405621468561161735381131)
              ·
                refine ⟨2108432202841742603071697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405621468561161735381131 2108432202841742603071697)
                ·
                  refine ⟨1581324152131306952303773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108432202841742603071697 1581324152131306952303773)
                  ·
                    refine ⟨592996557049240107113915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581324152131306952303773 592996557049240107113915)
                    ·
                      rfl

theorem cell22_1732285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_1732285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732285 prefixEnd_1732285 := by exact prefixLift 1732285
  have htrace : WordTrace (prefixWord ++ tailWord_1732285) baseStart_1732285 baseEnd_1732285 := by
    simpa [prefixWord, tailWord_1732285, baseEnd_1732285] using wordTrace_append hprefix tailTrace_1732285
  have hstable : (prefixWord ++ tailWord_1732285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732285).length < 2 ^ (prefixWord ++ tailWord_1732285).sum := by decide
  have hdescent : baseEnd_1732285 < baseStart_1732285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732330 : List Nat := [3, 1, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_1732330 : Nat := 118140960795 + 1732330 * 2 ^ 59
def prefixEnd_1732330 : Nat := 4983230072969 + 3 ^ 40 * 1732330 * 2
def baseEnd_1732330 : Nat := 593011961468874989738777

theorem tailTrace_1732330 : CollatzResearch.WordTrace tailWord_1732330 prefixEnd_1732330 593011961468874989738777 := by
  unfold tailWord_1732330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15795816453517935813654611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42122177209381162169745629 15795816453517935813654611)
  ·
    refine ⟨23693724680276903720481917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15795816453517935813654611 23693724680276903720481917)
    ·
      refine ⟨8885146755103838895180719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23693724680276903720481917 8885146755103838895180719)
      ·
        refine ⟨13327720132655758342771079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8885146755103838895180719 13327720132655758342771079)
        ·
          refine ⟨19991580198983637514156619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13327720132655758342771079 19991580198983637514156619)
          ·
            refine ⟨29987370298475456271234929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19991580198983637514156619 29987370298475456271234929)
            ·
              refine ⟨22490527723856592203426197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29987370298475456271234929 22490527723856592203426197)
              ·
                refine ⟨1054243487055777759535603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22490527723856592203426197 1054243487055777759535603)
                ·
                  refine ⟨1581365230583666639303405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054243487055777759535603 1581365230583666639303405)
                  ·
                    refine ⟨593011961468874989738777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581365230583666639303405 593011961468874989738777)
                    ·
                      rfl

theorem cell22_1732330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_1732330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732330 prefixEnd_1732330 := by exact prefixLift 1732330
  have htrace : WordTrace (prefixWord ++ tailWord_1732330) baseStart_1732330 baseEnd_1732330 := by
    simpa [prefixWord, tailWord_1732330, baseEnd_1732330] using wordTrace_append hprefix tailTrace_1732330
  have hstable : (prefixWord ++ tailWord_1732330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732330).length < 2 ^ (prefixWord ++ tailWord_1732330).sum := by decide
  have hdescent : baseEnd_1732330 < baseStart_1732330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732343 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 5]
def baseStart_1732343 : Nat := 118140960795 + 1732343 * 2 ^ 59
def prefixEnd_1732343 : Nat := 4983230072969 + 3 ^ 40 * 1732343 * 2
def baseEnd_1732343 : Nat := 197672137211515763054579

theorem tailTrace_1732343 : CollatzResearch.WordTrace tailWord_1732343 prefixEnd_1732343 197672137211515763054579 := by
  unfold tailWord_1732343
  simp only [CollatzResearch.WordTrace]
  refine ⟨63183739963024646474841683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42122493308683097649894455 63183739963024646474841683)
  ·
    refine ⟨94775609944536969712262525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63183739963024646474841683 94775609944536969712262525)
    ·
      refine ⟨35540853729201363642098447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94775609944536969712262525 35540853729201363642098447)
      ·
        refine ⟨53311280593802045463147671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35540853729201363642098447 53311280593802045463147671)
        ·
          refine ⟨79966920890703068194721507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53311280593802045463147671 79966920890703068194721507)
          ·
            refine ⟨119950381336054602292082261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79966920890703068194721507 119950381336054602292082261)
            ·
              refine ⟨1405668531281889870610339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 119950381336054602292082261 1405668531281889870610339)
              ·
                refine ⟨2108502796922834805915509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405668531281889870610339 2108502796922834805915509)
                ·
                  refine ⟨197672137211515763054579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2108502796922834805915509 197672137211515763054579)
                  ·
                    rfl

theorem cell22_1732343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 5].length) (baseStart_1732343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732343 prefixEnd_1732343 := by exact prefixLift 1732343
  have htrace : WordTrace (prefixWord ++ tailWord_1732343) baseStart_1732343 baseEnd_1732343 := by
    simpa [prefixWord, tailWord_1732343, baseEnd_1732343] using wordTrace_append hprefix tailTrace_1732343
  have hstable : (prefixWord ++ tailWord_1732343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732343).length < 2 ^ (prefixWord ++ tailWord_1732343).sum := by decide
  have hdescent : baseEnd_1732343 < baseStart_1732343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732437 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_1732437 : Nat := 118140960795 + 1732437 * 2 ^ 59
def prefixEnd_1732437 : Nat := 4983230072969 + 3 ^ 40 * 1732437 * 2
def baseEnd_1732437 : Nat := 593048589755562377313449

theorem tailTrace_1732437 : CollatzResearch.WordTrace tailWord_1732437 prefixEnd_1732437 593048589755562377313449 := by
  unfold tailWord_1732437
  simp only [CollatzResearch.WordTrace]
  refine ⟨63187168424684100528763565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42124778949789400352509043 63187168424684100528763565)
  ·
    refine ⟨23695188159256537698286337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63187168424684100528763565 23695188159256537698286337)
    ·
      refine ⟨17771391119442403273714753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23695188159256537698286337 17771391119442403273714753)
      ·
        refine ⟨13328543339581802455286065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17771391119442403273714753 13328543339581802455286065)
        ·
          refine ⟨9996407504686351841464549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13328543339581802455286065 9996407504686351841464549)
          ·
            refine ⟨1874326407128690970274603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9996407504686351841464549 1874326407128690970274603)
            ·
              refine ⟨2811489610693036455411905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874326407128690970274603 2811489610693036455411905)
              ·
                refine ⟨2108617208019777341558929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2811489610693036455411905 2108617208019777341558929)
                ·
                  refine ⟨1581462906014833006169197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108617208019777341558929 1581462906014833006169197)
                  ·
                    refine ⟨593048589755562377313449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581462906014833006169197 593048589755562377313449)
                    ·
                      rfl

theorem cell22_1732437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_1732437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732437 prefixEnd_1732437 := by exact prefixLift 1732437
  have htrace : WordTrace (prefixWord ++ tailWord_1732437) baseStart_1732437 baseEnd_1732437 := by
    simpa [prefixWord, tailWord_1732437, baseEnd_1732437] using wordTrace_append hprefix tailTrace_1732437
  have hstable : (prefixWord ++ tailWord_1732437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732437).length < 2 ^ (prefixWord ++ tailWord_1732437).sum := by decide
  have hdescent : baseEnd_1732437 < baseStart_1732437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732606 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1732606 : Nat := 118140960795 + 1732606 * 2 ^ 59
def prefixEnd_1732606 : Nat := 4983230072969 + 3 ^ 40 * 1732606 * 2
def baseEnd_1732606 : Nat := 593106441909302269837931

theorem tailTrace_1732606 : CollatzResearch.WordTrace tailWord_1732606 prefixEnd_1732606 593106441909302269837931 := by
  unfold tailWord_1732606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899166545133980298958209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42128888240714561594443781 7899166545133980298958209)
  ·
    refine ⟨5924374908850485224218657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7899166545133980298958209 5924374908850485224218657)
    ·
      refine ⟨4443281181637863918163993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5924374908850485224218657 4443281181637863918163993)
      ·
        refine ⟨3332460886228397938622995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4443281181637863918163993 3332460886228397938622995)
        ·
          refine ⟨4998691329342596907934493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3332460886228397938622995 4998691329342596907934493)
          ·
            refine ⟨1874509248503473840475435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4998691329342596907934493 1874509248503473840475435)
            ·
              refine ⟨2811763872755210760713153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874509248503473840475435 2811763872755210760713153)
              ·
                refine ⟨2108822904566408070534865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2811763872755210760713153 2108822904566408070534865)
                ·
                  refine ⟨1581617178424806052901149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108822904566408070534865 1581617178424806052901149)
                  ·
                    refine ⟨593106441909302269837931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581617178424806052901149 593106441909302269837931)
                    ·
                      rfl

theorem cell22_1732606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1732606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732606 prefixEnd_1732606 := by exact prefixLift 1732606
  have htrace : WordTrace (prefixWord ++ tailWord_1732606) baseStart_1732606 baseEnd_1732606 := by
    simpa [prefixWord, tailWord_1732606, baseEnd_1732606] using wordTrace_append hprefix tailTrace_1732606
  have hstable : (prefixWord ++ tailWord_1732606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732606).length < 2 ^ (prefixWord ++ tailWord_1732606).sum := by decide
  have hdescent : baseEnd_1732606 < baseStart_1732606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732722 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1732722 : Nat := 118140960795 + 1732722 * 2 ^ 59
def prefixEnd_1732722 : Nat := 4983230072969 + 3 ^ 40 * 1732722 * 2
def baseEnd_1732722 : Nat := 593146151079916633937575

theorem tailTrace_1732722 : CollatzResearch.WordTrace tailWord_1732722 prefixEnd_1732722 593146151079916633937575 := by
  unfold tailWord_1732722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799390807162898550722105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42131708819101062801925613 15799390807162898550722105)
  ·
    refine ⟨11849543105372173913041579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15799390807162898550722105 11849543105372173913041579)
    ·
      refine ⟨17774314658058260869562369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11849543105372173913041579 17774314658058260869562369)
      ·
        refine ⟨13330735993543695652171777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17774314658058260869562369 13330735993543695652171777)
        ·
          refine ⟨9998051995157771739128833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13330735993543695652171777 9998051995157771739128833)
          ·
            refine ⟨7498538996368328804346625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9998051995157771739128833 7498538996368328804346625)
            ·
              refine ⟨5623904247276246603259969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498538996368328804346625 5623904247276246603259969)
              ·
                refine ⟨4217928185457184952444977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5623904247276246603259969 4217928185457184952444977)
                ·
                  refine ⟨3163446139092888714333733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217928185457184952444977 3163446139092888714333733)
                  ·
                    refine ⟨593146151079916633937575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163446139092888714333733 593146151079916633937575)
                    ·
                      rfl

theorem cell22_1732722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1732722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732722 prefixEnd_1732722 := by exact prefixLift 1732722
  have htrace : WordTrace (prefixWord ++ tailWord_1732722) baseStart_1732722 baseEnd_1732722 := by
    simpa [prefixWord, tailWord_1732722, baseEnd_1732722] using wordTrace_append hprefix tailTrace_1732722
  have hstable : (prefixWord ++ tailWord_1732722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732722).length < 2 ^ (prefixWord ++ tailWord_1732722).sum := by decide
  have hdescent : baseEnd_1732722 < baseStart_1732722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732726 : List Nat := [5, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1732726 : Nat := 118140960795 + 1732726 * 2 ^ 59
def prefixEnd_1732726 : Nat := 4983230072969 + 3 ^ 40 * 1732726 * 2
def baseEnd_1732726 : Nat := 197715840120553985612521

theorem tailTrace_1732726 : CollatzResearch.WordTrace tailWord_1732726 prefixEnd_1732726 197715840120553985612521 := by
  unfold tailWord_1732726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949856820039818930377127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42131806080424735257356021 3949856820039818930377127)
  ·
    refine ⟨5924785230059728395565691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949856820039818930377127 5924785230059728395565691)
    ·
      refine ⟨8887177845089592593348537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5924785230059728395565691 8887177845089592593348537)
      ·
        refine ⟨6665383383817194445011403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8887177845089592593348537 6665383383817194445011403)
        ·
          refine ⟨9998075075725791667517105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6665383383817194445011403 9998075075725791667517105)
          ·
            refine ⟨7498556306794343750637829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9998075075725791667517105 7498556306794343750637829)
            ·
              refine ⟨1405979307523939453244593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7498556306794343750637829 1405979307523939453244593)
              ·
                refine ⟨1054484480642954589933445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405979307523939453244593 1054484480642954589933445)
                ·
                  refine ⟨197715840120553985612521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1054484480642954589933445 197715840120553985612521)
                  ·
                    rfl

theorem cell22_1732726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1732726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732726 prefixEnd_1732726 := by exact prefixLift 1732726
  have htrace : WordTrace (prefixWord ++ tailWord_1732726) baseStart_1732726 baseEnd_1732726 := by
    simpa [prefixWord, tailWord_1732726, baseEnd_1732726] using wordTrace_append hprefix tailTrace_1732726
  have hstable : (prefixWord ++ tailWord_1732726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732726).length < 2 ^ (prefixWord ++ tailWord_1732726).sum := by decide
  have hdescent : baseEnd_1732726 < baseStart_1732726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732752 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 3, 3]
def baseStart_1732752 : Nat := 118140960795 + 1732752 * 2 ^ 59
def prefixEnd_1732752 : Nat := 4983230072969 + 3 ^ 40 * 1732752 * 2
def baseEnd_1732752 : Nat := 593156420693006555687483

theorem tailTrace_1732752 : CollatzResearch.WordTrace tailWord_1732752 prefixEnd_1732752 593156420693006555687483 := by
  unfold tailWord_1732752
  simp only [CollatzResearch.WordTrace]
  refine ⟨31599328709271454663240255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42132438279028606217653673 31599328709271454663240255)
  ·
    refine ⟨47398993063907181994860383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31599328709271454663240255 47398993063907181994860383)
    ·
      refine ⟨71098489595860772992290575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47398993063907181994860383 71098489595860772992290575)
      ·
        refine ⟨106647734393791159488435863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71098489595860772992290575 106647734393791159488435863)
        ·
          refine ⟨159971601590686739232653795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106647734393791159488435863 159971601590686739232653795)
          ·
            refine ⟨239957402386030108848980693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159971601590686739232653795 239957402386030108848980693)
            ·
              refine ⟨5624001618422580676147985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239957402386030108848980693 5624001618422580676147985)
              ·
                refine ⟨4218001213816935507110989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5624001618422580676147985 4218001213816935507110989)
                ·
                  refine ⟨1581750455181350815166621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4218001213816935507110989 1581750455181350815166621)
                  ·
                    refine ⟨593156420693006555687483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581750455181350815166621 593156420693006555687483)
                    ·
                      rfl

theorem cell22_1732752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_1732752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732752 prefixEnd_1732752 := by exact prefixLift 1732752
  have htrace : WordTrace (prefixWord ++ tailWord_1732752) baseStart_1732752 baseEnd_1732752 := by
    simpa [prefixWord, tailWord_1732752, baseEnd_1732752] using wordTrace_append hprefix tailTrace_1732752
  have hstable : (prefixWord ++ tailWord_1732752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732752).length < 2 ^ (prefixWord ++ tailWord_1732752).sum := by decide
  have hdescent : baseEnd_1732752 < baseStart_1732752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732872 : List Nat := [2, 1, 3, 2, 3, 1, 2, 8]
def baseStart_1732872 : Nat := 118140960795 + 1732872 * 2 ^ 59
def prefixEnd_1732872 : Nat := 4983230072969 + 3 ^ 40 * 1732872 * 2
def baseEnd_1732872 : Nat := 65910833238374026965235

theorem tailTrace_1732872 : CollatzResearch.WordTrace tailWord_1732872 prefixEnd_1732872 65910833238374026965235 := by
  unfold tailWord_1732872
  simp only [CollatzResearch.WordTrace]
  refine ⟨31601517089054084910424435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42135356118738779880565913 31601517089054084910424435)
  ·
    refine ⟨47402275633581127365636653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31601517089054084910424435 47402275633581127365636653)
    ·
      refine ⟨17775853362592922762113745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47402275633581127365636653 17775853362592922762113745)
      ·
        refine ⟨13331890021944692071585309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17775853362592922762113745 13331890021944692071585309)
        ·
          refine ⟨4999458758229259526844491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13331890021944692071585309 4999458758229259526844491)
          ·
            refine ⟨7499188137343889290266737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999458758229259526844491 7499188137343889290266737)
            ·
              refine ⟨5624391103007916967700053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7499188137343889290266737 5624391103007916967700053)
              ·
                refine ⟨65910833238374026965235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5624391103007916967700053 65910833238374026965235)
                ·
                  rfl

theorem cell22_1732872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_1732872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732872 prefixEnd_1732872 := by exact prefixLift 1732872
  have htrace : WordTrace (prefixWord ++ tailWord_1732872) baseStart_1732872 baseEnd_1732872 := by
    simpa [prefixWord, tailWord_1732872, baseEnd_1732872] using wordTrace_append hprefix tailTrace_1732872
  have hstable : (prefixWord ++ tailWord_1732872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732872).length < 2 ^ (prefixWord ++ tailWord_1732872).sum := by decide
  have hdescent : baseEnd_1732872 < baseStart_1732872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732893 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1732893 : Nat := 118140960795 + 1732893 * 2 ^ 59
def prefixEnd_1732893 : Nat := 4983230072969 + 3 ^ 40 * 1732893 * 2
def baseEnd_1732893 : Nat := 593204687874529187912051

theorem tailTrace_1732893 : CollatzResearch.WordTrace tailWord_1732893 prefixEnd_1732893 593204687874529187912051 := by
  unfold tailWord_1732893
  simp only [CollatzResearch.WordTrace]
  refine ⟨63203800111032090407363333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42135866740688060271575555 63203800111032090407363333)
  ·
    refine ⟨11850712520818516951380625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63203800111032090407363333 11850712520818516951380625)
    ·
      refine ⟨8888034390613887713535469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11850712520818516951380625 8888034390613887713535469)
      ·
        refine ⟨3333012896480207892575801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8888034390613887713535469 3333012896480207892575801)
        ·
          refine ⟨2499759672360155919431851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3333012896480207892575801 2499759672360155919431851)
          ·
            refine ⟨3749639508540233879147777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499759672360155919431851 3749639508540233879147777)
            ·
              refine ⟨2812229631405175409360833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749639508540233879147777 2812229631405175409360833)
              ·
                refine ⟨2109172223553881557020625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812229631405175409360833 2109172223553881557020625)
                ·
                  refine ⟨1581879167665411167765469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2109172223553881557020625 1581879167665411167765469)
                  ·
                    refine ⟨593204687874529187912051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581879167665411167765469 593204687874529187912051)
                    ·
                      rfl

theorem cell22_1732893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1732893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732893 prefixEnd_1732893 := by exact prefixLift 1732893
  have htrace : WordTrace (prefixWord ++ tailWord_1732893) baseStart_1732893 baseEnd_1732893 := by
    simpa [prefixWord, tailWord_1732893, baseEnd_1732893] using wordTrace_append hprefix tailTrace_1732893
  have hstable : (prefixWord ++ tailWord_1732893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732893).length < 2 ^ (prefixWord ++ tailWord_1732893).sum := by decide
  have hdescent : baseEnd_1732893 < baseStart_1732893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732906 : List Nat := [3, 1, 4, 2, 2, 2, 1, 7]
def baseStart_1732906 : Nat := 118140960795 + 1732906 * 2 ^ 59
def prefixEnd_1732906 : Nat := 4983230072969 + 3 ^ 40 * 1732906 * 2
def baseEnd_1732906 : Nat := 65912126448911276370779

theorem tailTrace_1732906 : CollatzResearch.WordTrace tailWord_1732906 prefixEnd_1732906 65912126448911276370779 := by
  unfold tailWord_1732906
  simp only [CollatzResearch.WordTrace]
  refine ⟨15801068564996248406896643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42136182839989995751724381 15801068564996248406896643)
  ·
    refine ⟨23701602847494372610344965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15801068564996248406896643 23701602847494372610344965)
    ·
      refine ⟨4444050533905194864439681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23701602847494372610344965 4444050533905194864439681)
      ·
        refine ⟨3333037900428896148329761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4444050533905194864439681 3333037900428896148329761)
        ·
          refine ⟨2499778425321672111247321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3333037900428896148329761 2499778425321672111247321)
          ·
            refine ⟨1874833818991254083435491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2499778425321672111247321 1874833818991254083435491)
            ·
              refine ⟨2812250728486881125153237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874833818991254083435491 2812250728486881125153237)
              ·
                refine ⟨65912126448911276370779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2812250728486881125153237 65912126448911276370779)
                ·
                  rfl

theorem cell22_1732906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_1732906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732906 prefixEnd_1732906 := by exact prefixLift 1732906
  have htrace : WordTrace (prefixWord ++ tailWord_1732906) baseStart_1732906 baseEnd_1732906 := by
    simpa [prefixWord, tailWord_1732906, baseEnd_1732906] using wordTrace_append hprefix tailTrace_1732906
  have hstable : (prefixWord ++ tailWord_1732906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732906).length < 2 ^ (prefixWord ++ tailWord_1732906).sum := by decide
  have hdescent : baseEnd_1732906 < baseStart_1732906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732921 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 3, 3]
def baseStart_1732921 : Nat := 118140960795 + 1732921 * 2 ^ 59
def prefixEnd_1732921 : Nat := 4983230072969 + 3 ^ 40 * 1732921 * 2
def baseEnd_1732921 : Nat := 593214272846746448211965

theorem tailTrace_1732921 : CollatzResearch.WordTrace tailWord_1732921 prefixEnd_1732921 593214272846746448211965 := by
  unfold tailWord_1732921
  simp only [CollatzResearch.WordTrace]
  refine ⟨63204821354930651189382617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42136547569953767459588411 63204821354930651189382617)
  ·
    refine ⟨47403616016197988392036963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63204821354930651189382617 47403616016197988392036963)
    ·
      refine ⟨71105424024296982588055445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47403616016197988392036963 71105424024296982588055445)
      ·
        refine ⟨3333066751138921058815099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71105424024296982588055445 3333066751138921058815099)
        ·
          refine ⟨4999600126708381588222649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333066751138921058815099 4999600126708381588222649)
          ·
            refine ⟨3749700095031286191166987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4999600126708381588222649 3749700095031286191166987)
            ·
              refine ⟨5624550142546929286750481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749700095031286191166987 5624550142546929286750481)
              ·
                refine ⟨4218412606910196965062861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5624550142546929286750481 4218412606910196965062861)
                ·
                  refine ⟨1581904727591323861898573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4218412606910196965062861 1581904727591323861898573)
                  ·
                    refine ⟨593214272846746448211965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581904727591323861898573 593214272846746448211965)
                    ·
                      rfl

theorem cell22_1732921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_1732921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732921 prefixEnd_1732921 := by exact prefixLift 1732921
  have htrace : WordTrace (prefixWord ++ tailWord_1732921) baseStart_1732921 baseEnd_1732921 := by
    simpa [prefixWord, tailWord_1732921, baseEnd_1732921] using wordTrace_append hprefix tailTrace_1732921
  have hstable : (prefixWord ++ tailWord_1732921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732921).length < 2 ^ (prefixWord ++ tailWord_1732921).sum := by decide
  have hdescent : baseEnd_1732921 < baseStart_1732921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732947 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 5, 4]
def baseStart_1732947 : Nat := 118140960795 + 1732947 * 2 ^ 59
def prefixEnd_1732947 : Nat := 4983230072969 + 3 ^ 40 * 1732947 * 2
def baseEnd_1732947 : Nat := 593223173178091047061885

theorem tailTrace_1732947 : CollatzResearch.WordTrace tailWord_1732947 prefixEnd_1732947 593223173178091047061885 := by
  unfold tailWord_1732947
  simp only [CollatzResearch.WordTrace]
  refine ⟨63205769652836457629829095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42137179768557638419886063 63205769652836457629829095)
  ·
    refine ⟨94808654479254686444743643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63205769652836457629829095 94808654479254686444743643)
    ·
      refine ⟨142212981718882029667115465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94808654479254686444743643 142212981718882029667115465)
      ·
        refine ⟨106659736289161522250336599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142212981718882029667115465 106659736289161522250336599)
        ·
          refine ⟨159989604433742283375504899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106659736289161522250336599 159989604433742283375504899)
          ·
            refine ⟨239984406650613425063257349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159989604433742283375504899 239984406650613425063257349)
            ·
              refine ⟨44997076246990017199360753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239984406650613425063257349 44997076246990017199360753)
              ·
                refine ⟨33747807185242512899520565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44997076246990017199360753 33747807185242512899520565)
                ·
                  refine ⟨3163856923616485584330053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33747807185242512899520565 3163856923616485584330053)
                  ·
                    refine ⟨593223173178091047061885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163856923616485584330053 593223173178091047061885)
                    ·
                      rfl

theorem cell22_1732947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_1732947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732947 prefixEnd_1732947 := by exact prefixLift 1732947
  have htrace : WordTrace (prefixWord ++ tailWord_1732947) baseStart_1732947 baseEnd_1732947 := by
    simpa [prefixWord, tailWord_1732947, baseEnd_1732947] using wordTrace_append hprefix tailTrace_1732947
  have hstable : (prefixWord ++ tailWord_1732947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732947).length < 2 ^ (prefixWord ++ tailWord_1732947).sum := by decide
  have hdescent : baseEnd_1732947 < baseStart_1732947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732981 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1732981 : Nat := 118140960795 + 1732981 * 2 ^ 59
def prefixEnd_1732981 : Nat := 4983230072969 + 3 ^ 40 * 1732981 * 2
def baseEnd_1732981 : Nat := 593234812072926291711781

theorem tailTrace_1732981 : CollatzResearch.WordTrace tailWord_1732981 prefixEnd_1732981 593234812072926291711781 := by
  unfold tailWord_1732981
  simp only [CollatzResearch.WordTrace]
  refine ⟨63207009734713281436566797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42138006489808854291044531 63207009734713281436566797)
  ·
    refine ⟨23702628650517480538712549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63207009734713281436566797 23702628650517480538712549)
    ·
      refine ⟨4444242871972027601008603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23702628650517480538712549 4444242871972027601008603)
      ·
        refine ⟨6666364307958041401512905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444242871972027601008603 6666364307958041401512905)
        ·
          refine ⟨4999773230968531051134679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6666364307958041401512905 4999773230968531051134679)
          ·
            refine ⟨7499659846452796576702019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999773230968531051134679 7499659846452796576702019)
            ·
              refine ⟨11249489769679194865053029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7499659846452796576702019 11249489769679194865053029)
              ·
                refine ⟨2109279331814849037197443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11249489769679194865053029 2109279331814849037197443)
                ·
                  refine ⟨3163918997722273555796165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109279331814849037197443 3163918997722273555796165)
                  ·
                    refine ⟨593234812072926291711781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163918997722273555796165 593234812072926291711781)
                    ·
                      rfl

theorem cell22_1732981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1732981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1732981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1732981 prefixEnd_1732981 := by exact prefixLift 1732981
  have htrace : WordTrace (prefixWord ++ tailWord_1732981) baseStart_1732981 baseEnd_1732981 := by
    simpa [prefixWord, tailWord_1732981, baseEnd_1732981] using wordTrace_append hprefix tailTrace_1732981
  have hstable : (prefixWord ++ tailWord_1732981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732981).length < 2 ^ (prefixWord ++ tailWord_1732981).sum := by decide
  have hdescent : baseEnd_1732981 < baseStart_1732981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733024 : List Nat := [2, 1, 1, 4, 1, 4, 2, 7]
def baseStart_1733024 : Nat := 118140960795 + 1733024 * 2 ^ 59
def prefixEnd_1733024 : Nat := 4983230072969 + 3 ^ 40 * 1733024 * 2
def baseEnd_1733024 : Nat := 65916614650187612542961

theorem tailTrace_1733024 : CollatzResearch.WordTrace tailWord_1733024 prefixEnd_1733024 65916614650187612542961 := by
  unfold tailWord_1733024
  simp only [CollatzResearch.WordTrace]
  refine ⟨31604289036778749890191063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42139052049038333186921417 31604289036778749890191063)
  ·
    refine ⟨47406433555168124835286595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31604289036778749890191063 47406433555168124835286595)
    ·
      refine ⟨71109650332752187252929893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47406433555168124835286595 71109650332752187252929893)
      ·
        refine ⟨13333059437391035109924355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71109650332752187252929893 13333059437391035109924355)
        ·
          refine ⟨19999589156086552664886533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13333059437391035109924355 19999589156086552664886533)
          ·
            refine ⟨3749922966766228624666225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19999589156086552664886533 3749922966766228624666225)
            ·
              refine ⟨2812442225074671468499669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749922966766228624666225 2812442225074671468499669)
              ·
                refine ⟨65916614650187612542961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2812442225074671468499669 65916614650187612542961)
                ·
                  rfl

theorem cell22_1733024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_1733024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733024 prefixEnd_1733024 := by exact prefixLift 1733024
  have htrace : WordTrace (prefixWord ++ tailWord_1733024) baseStart_1733024 baseEnd_1733024 := by
    simpa [prefixWord, tailWord_1733024, baseEnd_1733024] using wordTrace_append hprefix tailTrace_1733024
  have hstable : (prefixWord ++ tailWord_1733024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733024).length < 2 ^ (prefixWord ++ tailWord_1733024).sum := by decide
  have hdescent : baseEnd_1733024 < baseStart_1733024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733028 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_1733028 : Nat := 118140960795 + 1733028 * 2 ^ 59
def prefixEnd_1733028 : Nat := 4983230072969 + 3 ^ 40 * 1733028 * 2
def baseEnd_1733028 : Nat := 593250901133433835786637

theorem tailTrace_1733028 : CollatzResearch.WordTrace tailWord_1733028 prefixEnd_1733028 593250901133433835786637 := by
  unfold tailWord_1733028
  simp only [CollatzResearch.WordTrace]
  refine ⟨31604361982771504231763869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42139149310362005642351825 31604361982771504231763869)
  ·
    refine ⟨11851635743539314086911451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31604361982771504231763869 11851635743539314086911451)
    ·
      refine ⟨17777453615308971130367177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11851635743539314086911451 17777453615308971130367177)
      ·
        refine ⟨13333090211481728347775383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17777453615308971130367177 13333090211481728347775383)
        ·
          refine ⟨19999635317222592521663075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13333090211481728347775383 19999635317222592521663075)
          ·
            refine ⟨29999452975833888782494613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19999635317222592521663075 29999452975833888782494613)
            ·
              refine ⟨1406224358242213536679435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29999452975833888782494613 1406224358242213536679435)
              ·
                refine ⟨2109336537363320305019153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406224358242213536679435 2109336537363320305019153)
                ·
                  refine ⟨1582002403022490228764365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2109336537363320305019153 1582002403022490228764365)
                  ·
                    refine ⟨593250901133433835786637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1582002403022490228764365 593250901133433835786637)
                    ·
                      rfl

theorem cell22_1733028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_1733028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733028 prefixEnd_1733028 := by exact prefixLift 1733028
  have htrace : WordTrace (prefixWord ++ tailWord_1733028) baseStart_1733028 baseEnd_1733028 := by
    simpa [prefixWord, tailWord_1733028, baseEnd_1733028] using wordTrace_append hprefix tailTrace_1733028
  have hstable : (prefixWord ++ tailWord_1733028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733028).length < 2 ^ (prefixWord ++ tailWord_1733028).sum := by decide
  have hdescent : baseEnd_1733028 < baseStart_1733028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733099 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 3, 4]
def baseStart_1733099 : Nat := 118140960795 + 1733099 * 2 ^ 59
def prefixEnd_1733099 : Nat := 4983230072969 + 3 ^ 40 * 1733099 * 2
def baseEnd_1733099 : Nat := 593275205884413317261419

theorem tailTrace_1733099 : CollatzResearch.WordTrace tailWord_1733099 prefixEnd_1733099 593275205884413317261419 := by
  unfold tailWord_1733099
  simp only [CollatzResearch.WordTrace]
  refine ⟨63211313548285787589362351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42140875698857191726241567 63211313548285787589362351)
  ·
    refine ⟨94816970322428681384043527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63211313548285787589362351 94816970322428681384043527)
    ·
      refine ⟨142225455483643022076065291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94816970322428681384043527 142225455483643022076065291)
      ·
        refine ⟨213338183225464533114097937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142225455483643022076065291 213338183225464533114097937)
        ·
          refine ⟨160003637419098399835573453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213338183225464533114097937 160003637419098399835573453)
          ·
            refine ⟨60001364032161899938340045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160003637419098399835573453 60001364032161899938340045)
            ·
              refine ⟨22500511512060712476877517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60001364032161899938340045 22500511512060712476877517)
              ·
                refine ⟨8437691817022767178829069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22500511512060712476877517 8437691817022767178829069)
                ·
                  refine ⟨3164134431383537692060901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8437691817022767178829069 3164134431383537692060901)
                  ·
                    refine ⟨593275205884413317261419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3164134431383537692060901 593275205884413317261419)
                    ·
                      rfl

theorem cell22_1733099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_1733099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733099 prefixEnd_1733099 := by exact prefixLift 1733099
  have htrace : WordTrace (prefixWord ++ tailWord_1733099) baseStart_1733099 baseEnd_1733099 := by
    simpa [prefixWord, tailWord_1733099, baseEnd_1733099] using wordTrace_append hprefix tailTrace_1733099
  have hstable : (prefixWord ++ tailWord_1733099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733099).length < 2 ^ (prefixWord ++ tailWord_1733099).sum := by decide
  have hdescent : baseEnd_1733099 < baseStart_1733099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733131 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 6]
def baseStart_1733131 : Nat := 118140960795 + 1733131 * 2 ^ 59
def prefixEnd_1733131 : Nat := 4983230072969 + 3 ^ 40 * 1733131 * 2
def baseEnd_1733131 : Nat := 197762053379458633487107

theorem tailTrace_1733131 : CollatzResearch.WordTrace tailWord_1733131 prefixEnd_1733131 197762053379458633487107 := by
  unfold tailWord_1733131
  simp only [CollatzResearch.WordTrace]
  refine ⟨63212480684169857054527247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42141653789446571369684831 63212480684169857054527247)
  ·
    refine ⟨94818721026254785581790871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63212480684169857054527247 94818721026254785581790871)
    ·
      refine ⟨142228081539382178372686307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94818721026254785581790871 142228081539382178372686307)
      ·
        refine ⟨213342122309073267559029461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142228081539382178372686307 213342122309073267559029461)
        ·
          refine ⟨5000205991618904708414753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 213342122309073267559029461 5000205991618904708414753)
          ·
            refine ⟨3750154493714178531311065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5000205991618904708414753 3750154493714178531311065)
            ·
              refine ⟨2812615870285633898483299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3750154493714178531311065 2812615870285633898483299)
              ·
                refine ⟨4218923805428450847724949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812615870285633898483299 4218923805428450847724949)
                ·
                  refine ⟨197762053379458633487107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4218923805428450847724949 197762053379458633487107)
                  ·
                    rfl

theorem cell22_1733131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 6].length) (baseStart_1733131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733131 prefixEnd_1733131 := by exact prefixLift 1733131
  have htrace : WordTrace (prefixWord ++ tailWord_1733131) baseStart_1733131 baseEnd_1733131 := by
    simpa [prefixWord, tailWord_1733131, baseEnd_1733131] using wordTrace_append hprefix tailTrace_1733131
  have hstable : (prefixWord ++ tailWord_1733131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733131).length < 2 ^ (prefixWord ++ tailWord_1733131).sum := by decide
  have hdescent : baseEnd_1733131 < baseStart_1733131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733146 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_1733146 : Nat := 118140960795 + 1733146 * 2 ^ 59
def prefixEnd_1733146 : Nat := 4983230072969 + 3 ^ 40 * 1733146 * 2
def baseEnd_1733146 : Nat := 593291294944920861336275

theorem tailTrace_1733146 : CollatzResearch.WordTrace tailWord_1733146 prefixEnd_1733146 593291294944920861336275 := by
  unfold tailWord_1733146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15803256944778878654080823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42142018519410343077548861 15803256944778878654080823)
  ·
    refine ⟨23704885417168317981121235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15803256944778878654080823 23704885417168317981121235)
    ·
      refine ⟨35557328125752476971681853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23704885417168317981121235 35557328125752476971681853)
      ·
        refine ⟨13333998047157178864380695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35557328125752476971681853 13333998047157178864380695)
        ·
          refine ⟨20000997070735768296571043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13333998047157178864380695 20000997070735768296571043)
          ·
            refine ⟨30001495606103652444856565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20000997070735768296571043 30001495606103652444856565)
            ·
              refine ⟨2812640213072217416705303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30001495606103652444856565 2812640213072217416705303)
              ·
                refine ⟨4218960319608326125057955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812640213072217416705303 4218960319608326125057955)
                ·
                  refine ⟨6328440479412489187586933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218960319608326125057955 6328440479412489187586933)
                  ·
                    refine ⟨593291294944920861336275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6328440479412489187586933 593291294944920861336275)
                    ·
                      rfl

theorem cell22_1733146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_1733146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733146 prefixEnd_1733146 := by exact prefixLift 1733146
  have htrace : WordTrace (prefixWord ++ tailWord_1733146) baseStart_1733146 baseEnd_1733146 := by
    simpa [prefixWord, tailWord_1733146, baseEnd_1733146] using wordTrace_append hprefix tailTrace_1733146
  have hstable : (prefixWord ++ tailWord_1733146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733146).length < 2 ^ (prefixWord ++ tailWord_1733146).sum := by decide
  have hdescent : baseEnd_1733146 < baseStart_1733146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733182 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1733182 : Nat := 118140960795 + 1733182 * 2 ^ 59
def prefixEnd_1733182 : Nat := 4983230072969 + 3 ^ 40 * 1733182 * 2
def baseEnd_1733182 : Nat := 197767872826876255812055

theorem tailTrace_1733182 : CollatzResearch.WordTrace tailWord_1733182 prefixEnd_1733182 197767872826876255812055 := by
  unfold tailWord_1733182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7901792600873136595579225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42142893871323395176422533 7901792600873136595579225)
  ·
    refine ⟨5926344450654852446684419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7901792600873136595579225 5926344450654852446684419)
    ·
      refine ⟨8889516675982278670026629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5926344450654852446684419 8889516675982278670026629)
      ·
        refine ⟨1666784376746677250629993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8889516675982278670026629 1666784376746677250629993)
        ·
          refine ⟨1250088282560007937972495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1666784376746677250629993 1250088282560007937972495)
          ·
            refine ⟨1875132423840011906958743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250088282560007937972495 1875132423840011906958743)
            ·
              refine ⟨2812698635760017860438115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875132423840011906958743 2812698635760017860438115)
              ·
                refine ⟨4219047953640026790657173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812698635760017860438115 4219047953640026790657173)
                ·
                  refine ⟨197767872826876255812055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4219047953640026790657173 197767872826876255812055)
                  ·
                    rfl

theorem cell22_1733182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1733182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733182 prefixEnd_1733182 := by exact prefixLift 1733182
  have htrace : WordTrace (prefixWord ++ tailWord_1733182) baseStart_1733182 baseEnd_1733182 := by
    simpa [prefixWord, tailWord_1733182, baseEnd_1733182] using wordTrace_append hprefix tailTrace_1733182
  have hstable : (prefixWord ++ tailWord_1733182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733182).length < 2 ^ (prefixWord ++ tailWord_1733182).sum := by decide
  have hdescent : baseEnd_1733182 < baseStart_1733182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733197 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1733197 : Nat := 118140960795 + 1733197 * 2 ^ 59
def prefixEnd_1733197 : Nat := 4983230072969 + 3 ^ 40 * 1733197 * 2
def baseEnd_1733197 : Nat := 593308753287173728311119

theorem tailTrace_1733197 : CollatzResearch.WordTrace tailWord_1733197 prefixEnd_1733197 593308753287173728311119 := by
  unfold tailWord_1733197
  simp only [CollatzResearch.WordTrace]
  refine ⟨63214887901930750326429845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42143258601287166884286563 63214887901930750326429845)
  ·
    refine ⟨2963197870403003921551399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63214887901930750326429845 2963197870403003921551399)
    ·
      refine ⟨4444796805604505882327099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963197870403003921551399 4444796805604505882327099)
      ·
        refine ⟨6667195208406758823490649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444796805604505882327099 6667195208406758823490649)
        ·
          refine ⟨5000396406305069117617987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6667195208406758823490649 5000396406305069117617987)
          ·
            refine ⟨7500594609457603676426981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000396406305069117617987 7500594609457603676426981)
            ·
              refine ⟨1406361489273300689330059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7500594609457603676426981 1406361489273300689330059)
              ·
                refine ⟨2109542233909951033995089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406361489273300689330059 2109542233909951033995089)
                ·
                  refine ⟨1582156675432463275496317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2109542233909951033995089 1582156675432463275496317)
                  ·
                    refine ⟨593308753287173728311119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1582156675432463275496317 593308753287173728311119)
                    ·
                      rfl

theorem cell22_1733197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1733197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733197 prefixEnd_1733197 := by exact prefixLift 1733197
  have htrace : WordTrace (prefixWord ++ tailWord_1733197) baseStart_1733197 baseEnd_1733197 := by
    simpa [prefixWord, tailWord_1733197, baseEnd_1733197] using wordTrace_append hprefix tailTrace_1733197
  have hstable : (prefixWord ++ tailWord_1733197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733197).length < 2 ^ (prefixWord ++ tailWord_1733197).sum := by decide
  have hdescent : baseEnd_1733197 < baseStart_1733197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733251 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 3, 4]
def baseStart_1733251 : Nat := 118140960795 + 1733251 * 2 ^ 59
def prefixEnd_1733251 : Nat := 4983230072969 + 3 ^ 40 * 1733251 * 2
def baseEnd_1733251 : Nat := 593327238590735587460953

theorem tailTrace_1733251 : CollatzResearch.WordTrace tailWord_1733251 prefixEnd_1733251 593327238590735587460953 := by
  unfold tailWord_1733251
  simp only [CollatzResearch.WordTrace]
  refine ⟨63216857443735117548895607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42144571629156745032597071 63216857443735117548895607)
  ·
    refine ⟨94825286165602676323343411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63216857443735117548895607 94825286165602676323343411)
    ·
      refine ⟨142237929248404014485015117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94825286165602676323343411 142237929248404014485015117)
      ·
        refine ⟨53339223468151505431880669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142237929248404014485015117 53339223468151505431880669)
        ·
          refine ⟨20002208800556814536955251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53339223468151505431880669 20002208800556814536955251)
          ·
            refine ⟨30003313200835221805432877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20002208800556814536955251 30003313200835221805432877)
            ·
              refine ⟨11251242450313208177037329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30003313200835221805432877 11251242450313208177037329)
              ·
                refine ⟨8438431837734906132777997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11251242450313208177037329 8438431837734906132777997)
                ·
                  refine ⟨3164411939150589799791749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8438431837734906132777997 3164411939150589799791749)
                  ·
                    refine ⟨593327238590735587460953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3164411939150589799791749 593327238590735587460953)
                    ·
                      rfl

theorem cell22_1733251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_1733251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733251 prefixEnd_1733251 := by exact prefixLift 1733251
  have htrace : WordTrace (prefixWord ++ tailWord_1733251) baseStart_1733251 baseEnd_1733251 := by
    simpa [prefixWord, tailWord_1733251, baseEnd_1733251] using wordTrace_append hprefix tailTrace_1733251
  have hstable : (prefixWord ++ tailWord_1733251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733251).length < 2 ^ (prefixWord ++ tailWord_1733251).sum := by decide
  have hdescent : baseEnd_1733251 < baseStart_1733251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733296 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_1733296 : Nat := 118140960795 + 1733296 * 2 ^ 59
def prefixEnd_1733296 : Nat := 4983230072969 + 3 ^ 40 * 1733296 * 2
def baseEnd_1733296 : Nat := 593342643010370470085815

theorem tailTrace_1733296 : CollatzResearch.WordTrace tailWord_1733296 prefixEnd_1733296 593342643010370470085815 := by
  unfold tailWord_1733296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31609249364286045117141871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42145665819048060156189161 31609249364286045117141871)
  ·
    refine ⟨47413874046429067675712807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31609249364286045117141871 47413874046429067675712807)
    ·
      refine ⟨71120811069643601513569211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47413874046429067675712807 71120811069643601513569211)
      ·
        refine ⟨106681216604465402270353817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71120811069643601513569211 106681216604465402270353817)
        ·
          refine ⟨80010912453349051702765363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106681216604465402270353817 80010912453349051702765363)
          ·
            refine ⟨120016368680023577554148045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80010912453349051702765363 120016368680023577554148045)
            ·
              refine ⟨45006138255008841582805517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120016368680023577554148045 45006138255008841582805517)
              ·
                refine ⟨16877301845628315593552069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45006138255008841582805517 16877301845628315593552069)
                ·
                  refine ⟨3164494096055309173791013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16877301845628315593552069 3164494096055309173791013)
                  ·
                    refine ⟨593342643010370470085815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3164494096055309173791013 593342643010370470085815)
                    ·
                      rfl

theorem cell22_1733296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_1733296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733296 prefixEnd_1733296 := by exact prefixLift 1733296
  have htrace : WordTrace (prefixWord ++ tailWord_1733296) baseStart_1733296 baseEnd_1733296 := by
    simpa [prefixWord, tailWord_1733296, baseEnd_1733296] using wordTrace_append hprefix tailTrace_1733296
  have hstable : (prefixWord ++ tailWord_1733296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733296).length < 2 ^ (prefixWord ++ tailWord_1733296).sum := by decide
  have hdescent : baseEnd_1733296 < baseStart_1733296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733371 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 6, 5]
def baseStart_1733371 : Nat := 118140960795 + 1733371 * 2 ^ 59
def prefixEnd_1733371 : Nat := 4983230072969 + 3 ^ 40 * 1733371 * 2
def baseEnd_1733371 : Nat := 593368317043095274460585

theorem tailTrace_1733371 : CollatzResearch.WordTrace tailWord_1733371 prefixEnd_1733371 593368317043095274460585 := by
  unfold tailWord_1733371
  simp only [CollatzResearch.WordTrace]
  refine ⟨63221234203300378043263967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42147489468866918695509311 63221234203300378043263967)
  ·
    refine ⟨94831851304950567064895951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63221234203300378043263967 94831851304950567064895951)
    ·
      refine ⟨142247776957425850597343927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94831851304950567064895951 142247776957425850597343927)
      ·
        refine ⟨213371665436138775896015891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142247776957425850597343927 213371665436138775896015891)
        ·
          refine ⟨320057498154208163844023837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213371665436138775896015891 320057498154208163844023837)
          ·
            refine ⟨120021561807828061441508939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320057498154208163844023837 120021561807828061441508939)
            ·
              refine ⟨180032342711742092162263409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120021561807828061441508939 180032342711742092162263409)
              ·
                refine ⟨135024257033806569121697557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180032342711742092162263409 135024257033806569121697557)
                ·
                  refine ⟨6329262048459682927579573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135024257033806569121697557 6329262048459682927579573)
                  ·
                    refine ⟨593368317043095274460585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6329262048459682927579573 593368317043095274460585)
                    ·
                      rfl

theorem cell22_1733371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_1733371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733371 prefixEnd_1733371 := by exact prefixLift 1733371
  have htrace : WordTrace (prefixWord ++ tailWord_1733371) baseStart_1733371 baseEnd_1733371 := by
    simpa [prefixWord, tailWord_1733371, baseEnd_1733371] using wordTrace_append hprefix tailTrace_1733371
  have hstable : (prefixWord ++ tailWord_1733371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733371).length < 2 ^ (prefixWord ++ tailWord_1733371).sum := by decide
  have hdescent : baseEnd_1733371 < baseStart_1733371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733373 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 5]
def baseStart_1733373 : Nat := 118140960795 + 1733373 * 2 ^ 59
def prefixEnd_1733373 : Nat := 4983230072969 + 3 ^ 40 * 1733373 * 2
def baseEnd_1733373 : Nat := 197789667227989311970193

theorem tailTrace_1733373 : CollatzResearch.WordTrace tailWord_1733373 prefixEnd_1733373 197789667227989311970193 := by
  unfold tailWord_1733373
  simp only [CollatzResearch.WordTrace]
  refine ⟨63221307149293132384836773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42147538099528754923224515 63221307149293132384836773)
  ·
    refine ⟨11853995090492462322156895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63221307149293132384836773 11853995090492462322156895)
    ·
      refine ⟨17780992635738693483235343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11853995090492462322156895 17780992635738693483235343)
      ·
        refine ⟨26671488953608040224853015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17780992635738693483235343 26671488953608040224853015)
        ·
          refine ⟨40007233430412060337279523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26671488953608040224853015 40007233430412060337279523)
          ·
            refine ⟨60010850145618090505919285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40007233430412060337279523 60010850145618090505919285)
            ·
              refine ⟨5626017201151695984929933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60010850145618090505919285 5626017201151695984929933)
              ·
                refine ⟨2109756450431885994348725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5626017201151695984929933 2109756450431885994348725)
                ·
                  refine ⟨197789667227989311970193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2109756450431885994348725 197789667227989311970193)
                  ·
                    rfl

theorem cell22_1733373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_1733373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733373 prefixEnd_1733373 := by exact prefixLift 1733373
  have htrace : WordTrace (prefixWord ++ tailWord_1733373) baseStart_1733373 baseEnd_1733373 := by
    simpa [prefixWord, tailWord_1733373, baseEnd_1733373] using wordTrace_append hprefix tailTrace_1733373
  have hstable : (prefixWord ++ tailWord_1733373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733373).length < 2 ^ (prefixWord ++ tailWord_1733373).sum := by decide
  have hdescent : baseEnd_1733373 < baseStart_1733373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733401 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 10]
def baseStart_1733401 : Nat := 118140960795 + 1733401 * 2 ^ 59
def prefixEnd_1733401 : Nat := 4983230072969 + 3 ^ 40 * 1733401 * 2
def baseEnd_1733401 : Nat := 197792862218728398736831

theorem tailTrace_1733401 : CollatzResearch.WordTrace tailWord_1733401 prefixEnd_1733401 197792862218728398736831 := by
  unfold tailWord_1733401
  simp only [CollatzResearch.WordTrace]
  refine ⟨63222328393191693166856057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42148218928794462111237371 63222328393191693166856057)
  ·
    refine ⟨47416746294893769875142043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63222328393191693166856057 47416746294893769875142043)
    ·
      refine ⟨71125119442340654812713065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47416746294893769875142043 71125119442340654812713065)
      ·
        refine ⟨53343839581755491109534799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71125119442340654812713065 53343839581755491109534799)
        ·
          refine ⟨80015759372633236664302199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53343839581755491109534799 80015759372633236664302199)
          ·
            refine ⟨120023639058949854996453299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80015759372633236664302199 120023639058949854996453299)
            ·
              refine ⟨180035458588424782494679949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120023639058949854996453299 180035458588424782494679949)
              ·
                refine ⟨67513296970659293435504981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180035458588424782494679949 67513296970659293435504981)
                ·
                  refine ⟨197792862218728398736831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67513296970659293435504981 197792862218728398736831)
                  ·
                    rfl

theorem cell22_1733401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_1733401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733401 prefixEnd_1733401 := by exact prefixLift 1733401
  have htrace : WordTrace (prefixWord ++ tailWord_1733401) baseStart_1733401 baseEnd_1733401 := by
    simpa [prefixWord, tailWord_1733401, baseEnd_1733401] using wordTrace_append hprefix tailTrace_1733401
  have hstable : (prefixWord ++ tailWord_1733401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733401).length < 2 ^ (prefixWord ++ tailWord_1733401).sum := by decide
  have hdescent : baseEnd_1733401 < baseStart_1733401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733448 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_1733448 : Nat := 118140960795 + 1733448 * 2 ^ 59
def prefixEnd_1733448 : Nat := 4983230072969 + 3 ^ 40 * 1733448 * 2
def baseEnd_1733448 : Nat := 593394675716692740285349

theorem tailTrace_1733448 : CollatzResearch.WordTrace tailWord_1733448 prefixEnd_1733448 593394675716692740285349 := by
  unfold tailWord_1733448
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612021312010710096908499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42149361749347613462544665 31612021312010710096908499)
  ·
    refine ⟨47418031968016065145362749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31612021312010710096908499 47418031968016065145362749)
    ·
      refine ⟨17781761988006024429511031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47418031968016065145362749 17781761988006024429511031)
      ·
        refine ⟨26672642982009036644266547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17781761988006024429511031 26672642982009036644266547)
        ·
          refine ⟨40008964473013554966399821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26672642982009036644266547 40008964473013554966399821)
          ·
            refine ⟨15003361677380083112399933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40008964473013554966399821 15003361677380083112399933)
            ·
              refine ⟨5626260629017531167149975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15003361677380083112399933 5626260629017531167149975)
              ·
                refine ⟨8439390943526296750724963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626260629017531167149975 8439390943526296750724963)
                ·
                  refine ⟨12659086415289445126087445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8439390943526296750724963 12659086415289445126087445)
                  ·
                    refine ⟨593394675716692740285349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12659086415289445126087445 593394675716692740285349)
                    ·
                      rfl

theorem cell22_1733448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_1733448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733448 prefixEnd_1733448 := by exact prefixLift 1733448
  have htrace : WordTrace (prefixWord ++ tailWord_1733448) baseStart_1733448 baseEnd_1733448 := by
    simpa [prefixWord, tailWord_1733448, baseEnd_1733448] using wordTrace_append hprefix tailTrace_1733448
  have hstable : (prefixWord ++ tailWord_1733448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733448).length < 2 ^ (prefixWord ++ tailWord_1733448).sum := by decide
  have hdescent : baseEnd_1733448 < baseStart_1733448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733452 : List Nat := [2, 2, 1, 3, 3, 2, 2, 3, 4]
def baseStart_1733452 : Nat := 118140960795 + 1733452 * 2 ^ 59
def prefixEnd_1733452 : Nat := 4983230072969 + 3 ^ 40 * 1733452 * 2
def baseEnd_1733452 : Nat := 197798681666146021061779

theorem tailTrace_1733452 : CollatzResearch.WordTrace tailWord_1733452 prefixEnd_1733452 197798681666146021061779 := by
  unfold tailWord_1733452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612094258003464438481305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42149459010671285917975073 31612094258003464438481305)
  ·
    refine ⟨23709070693502598328860979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31612094258003464438481305 23709070693502598328860979)
    ·
      refine ⟨35563606040253897493291469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23709070693502598328860979 35563606040253897493291469)
      ·
        refine ⟨13336352265095211559984301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35563606040253897493291469 13336352265095211559984301)
        ·
          refine ⟨5001132099410704334994113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13336352265095211559984301 5001132099410704334994113)
          ·
            refine ⟨3750849074558028251245585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5001132099410704334994113 3750849074558028251245585)
            ·
              refine ⟨2813136805918521188434189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3750849074558028251245585 2813136805918521188434189)
              ·
                refine ⟨1054926302219445445662821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2813136805918521188434189 1054926302219445445662821)
                ·
                  refine ⟨197798681666146021061779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1054926302219445445662821 197798681666146021061779)
                  ·
                    rfl

theorem cell22_1733452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_1733452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733452 prefixEnd_1733452 := by exact prefixLift 1733452
  have htrace : WordTrace (prefixWord ++ tailWord_1733452) baseStart_1733452 baseEnd_1733452 := by
    simpa [prefixWord, tailWord_1733452, baseEnd_1733452] using wordTrace_append hprefix tailTrace_1733452
  have hstable : (prefixWord ++ tailWord_1733452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733452).length < 2 ^ (prefixWord ++ tailWord_1733452).sum := by decide
  have hdescent : baseEnd_1733452 < baseStart_1733452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733463 : List Nat := [1, 1, 3, 2, 4, 2, 9]
def baseStart_1733463 : Nat := 118140960795 + 1733463 * 2 ^ 59
def prefixEnd_1733463 : Nat := 4983230072969 + 3 ^ 40 * 1733463 * 2
def baseEnd_1733463 : Nat := 21977770760119914857789

theorem tailTrace_1733463 : CollatzResearch.WordTrace tailWord_1733463 prefixEnd_1733463 21977770760119914857789 := by
  unfold tailWord_1733463
  simp only [CollatzResearch.WordTrace]
  refine ⟨63224589718967077755613043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42149726479311385170408695 63224589718967077755613043)
  ·
    refine ⟨94836884578450616633419565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63224589718967077755613043 94836884578450616633419565)
    ·
      refine ⟨35563831716918981237532337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94836884578450616633419565 35563831716918981237532337)
      ·
        refine ⟨26672873787689235928149253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35563831716918981237532337 26672873787689235928149253)
        ·
          refine ⟨5001163835191731736527985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26672873787689235928149253 5001163835191731736527985)
          ·
            refine ⟨3750872876393798802395989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5001163835191731736527985 3750872876393798802395989)
            ·
              refine ⟨21977770760119914857789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3750872876393798802395989 21977770760119914857789)
              ·
                rfl

theorem cell22_1733463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 9].length) (baseStart_1733463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733463 prefixEnd_1733463 := by exact prefixLift 1733463
  have htrace : WordTrace (prefixWord ++ tailWord_1733463) baseStart_1733463 baseEnd_1733463 := by
    simpa [prefixWord, tailWord_1733463, baseEnd_1733463] using wordTrace_append hprefix tailTrace_1733463
  have hstable : (prefixWord ++ tailWord_1733463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733463).length < 2 ^ (prefixWord ++ tailWord_1733463).sum := by decide
  have hdescent : baseEnd_1733463 < baseStart_1733463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733523 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 2, 5]
def baseStart_1733523 : Nat := 118140960795 + 1733523 * 2 ^ 59
def prefixEnd_1733523 : Nat := 4983230072969 + 3 ^ 40 * 1733523 * 2
def baseEnd_1733523 : Nat := 593420349749417544660119

theorem tailTrace_1733523 : CollatzResearch.WordTrace tailWord_1733523 prefixEnd_1733523 593420349749417544660119 := by
  unfold tailWord_1733523
  simp only [CollatzResearch.WordTrace]
  refine ⟨63226778098749708002797223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42151185399166472001864815 63226778098749708002797223)
  ·
    refine ⟨94840167148124562004195835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63226778098749708002797223 94840167148124562004195835)
    ·
      refine ⟨142260250722186843006293753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94840167148124562004195835 142260250722186843006293753)
      ·
        refine ⟨106695188041640132254720315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142260250722186843006293753 106695188041640132254720315)
        ·
          refine ⟨160042782062460198382080473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106695188041640132254720315 160042782062460198382080473)
          ·
            refine ⟨120032086546845148786560355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160042782062460198382080473 120032086546845148786560355)
            ·
              refine ⟨180048129820267723179840533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120032086546845148786560355 180048129820267723179840533)
              ·
                refine ⟨8439756085325049524055025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180048129820267723179840533 8439756085325049524055025)
                ·
                  refine ⟨6329817063993787143041269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8439756085325049524055025 6329817063993787143041269)
                  ·
                    refine ⟨593420349749417544660119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6329817063993787143041269 593420349749417544660119)
                    ·
                      rfl

theorem cell22_1733523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_1733523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733523 prefixEnd_1733523 := by exact prefixLift 1733523
  have htrace : WordTrace (prefixWord ++ tailWord_1733523) baseStart_1733523 baseEnd_1733523 := by
    simpa [prefixWord, tailWord_1733523, baseEnd_1733523] using wordTrace_append hprefix tailTrace_1733523
  have hstable : (prefixWord ++ tailWord_1733523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733523).length < 2 ^ (prefixWord ++ tailWord_1733523).sum := by decide
  have hdescent : baseEnd_1733523 < baseStart_1733523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733555 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 1, 4]
def baseStart_1733555 : Nat := 118140960795 + 1733555 * 2 ^ 59
def prefixEnd_1733555 : Nat := 4983230072969 + 3 ^ 40 * 1733555 * 2
def baseEnd_1733555 : Nat := 593431304003380127860021

theorem tailTrace_1733555 : CollatzResearch.WordTrace tailWord_1733555 prefixEnd_1733555 593431304003380127860021 := by
  unfold tailWord_1733555
  simp only [CollatzResearch.WordTrace]
  refine ⟨63227945234633777467962119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42151963489755851645308079 63227945234633777467962119)
  ·
    refine ⟨94841917851950666201943179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63227945234633777467962119 94841917851950666201943179)
    ·
      refine ⟨142262876777925999302914769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94841917851950666201943179 142262876777925999302914769)
      ·
        refine ⟨106697157583444499477186077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142262876777925999302914769 106697157583444499477186077)
        ·
          refine ⟨40011434093791687303944779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106697157583444499477186077 40011434093791687303944779)
          ·
            refine ⟨60017151140687530955917169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40011434093791687303944779 60017151140687530955917169)
            ·
              refine ⟨45012863355515648216937877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60017151140687530955917169 45012863355515648216937877)
              ·
                refine ⟨2109977969789796010168963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45012863355515648216937877 2109977969789796010168963)
                ·
                  refine ⟨3164966954684694015253445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109977969789796010168963 3164966954684694015253445)
                  ·
                    refine ⟨593431304003380127860021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3164966954684694015253445 593431304003380127860021)
                    ·
                      rfl

theorem cell22_1733555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 4].length) (baseStart_1733555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733555 prefixEnd_1733555 := by exact prefixLift 1733555
  have htrace : WordTrace (prefixWord ++ tailWord_1733555) baseStart_1733555 baseEnd_1733555 := by
    simpa [prefixWord, tailWord_1733555, baseEnd_1733555] using wordTrace_append hprefix tailTrace_1733555
  have hstable : (prefixWord ++ tailWord_1733555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733555).length < 2 ^ (prefixWord ++ tailWord_1733555).sum := by decide
  have hdescent : baseEnd_1733555 < baseStart_1733555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733617 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_1733617 : Nat := 118140960795 + 1733617 * 2 ^ 59
def prefixEnd_1733617 : Nat := 4983230072969 + 3 ^ 40 * 1733617 * 2
def baseEnd_1733617 : Nat := 593452527870432632809831

theorem tailTrace_1733617 : CollatzResearch.WordTrace tailWord_1733617 prefixEnd_1733617 593452527870432632809831 := by
  unfold tailWord_1733617
  simp only [CollatzResearch.WordTrace]
  refine ⟨63230206560409162056719105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42153471040272774704479403 63230206560409162056719105)
  ·
    refine ⟨47422654920306871542539329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63230206560409162056719105 47422654920306871542539329)
    ·
      refine ⟨35566991190230153656904497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47422654920306871542539329 35566991190230153656904497)
      ·
        refine ⟨26675243392672615242678373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35566991190230153656904497 26675243392672615242678373)
        ·
          refine ⟨5001608136126115358002195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26675243392672615242678373 5001608136126115358002195)
          ·
            refine ⟨7502412204189173037003293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001608136126115358002195 7502412204189173037003293)
            ·
              refine ⟨2813404576570939888876235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7502412204189173037003293 2813404576570939888876235)
              ·
                refine ⟨4220106864856409833314353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813404576570939888876235 4220106864856409833314353)
                ·
                  refine ⟨3165080148642307374985765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220106864856409833314353 3165080148642307374985765)
                  ·
                    refine ⟨593452527870432632809831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165080148642307374985765 593452527870432632809831)
                    ·
                      rfl

theorem cell22_1733617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_1733617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733617 prefixEnd_1733617 := by exact prefixLift 1733617
  have htrace : WordTrace (prefixWord ++ tailWord_1733617) baseStart_1733617 baseEnd_1733617 := by
    simpa [prefixWord, tailWord_1733617, baseEnd_1733617] using wordTrace_append hprefix tailTrace_1733617
  have hstable : (prefixWord ++ tailWord_1733617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733617).length < 2 ^ (prefixWord ++ tailWord_1733617).sum := by decide
  have hdescent : baseEnd_1733617 < baseStart_1733617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733705 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 6]
def baseStart_1733705 : Nat := 118140960795 + 1733705 * 2 ^ 59
def prefixEnd_1733705 : Nat := 4983230072969 + 3 ^ 40 * 1733705 * 2
def baseEnd_1733705 : Nat := 197827550689609912203187

theorem tailTrace_1733705 : CollatzResearch.WordTrace tailWord_1733705 prefixEnd_1733705 197827550689609912203187 := by
  unfold tailWord_1733705
  simp only [CollatzResearch.WordTrace]
  refine ⟨63233416184090353085922569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42155610789393568723948379 63233416184090353085922569)
  ·
    refine ⟨47425062138067764814441927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63233416184090353085922569 47425062138067764814441927)
    ·
      refine ⟨71137593207101647221662891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47425062138067764814441927 71137593207101647221662891)
      ·
        refine ⟨106706389810652470832494337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71137593207101647221662891 106706389810652470832494337)
        ·
          refine ⟨80029792357989353124370753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106706389810652470832494337 80029792357989353124370753)
          ·
            refine ⟨60022344268492014843278065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80029792357989353124370753 60022344268492014843278065)
            ·
              refine ⟨45016758201369011132458549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60022344268492014843278065 45016758201369011132458549)
              ·
                refine ⟨4220321081378344793667989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45016758201369011132458549 4220321081378344793667989)
                ·
                  refine ⟨197827550689609912203187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4220321081378344793667989 197827550689609912203187)
                  ·
                    rfl

theorem cell22_1733705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_1733705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733705 prefixEnd_1733705 := by exact prefixLift 1733705
  have htrace : WordTrace (prefixWord ++ tailWord_1733705) baseStart_1733705 baseEnd_1733705 := by
    simpa [prefixWord, tailWord_1733705, baseEnd_1733705] using wordTrace_append hprefix tailTrace_1733705
  have hstable : (prefixWord ++ tailWord_1733705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733705).length < 2 ^ (prefixWord ++ tailWord_1733705).sum := by decide
  have hdescent : baseEnd_1733705 < baseStart_1733705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733737 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_1733737 : Nat := 118140960795 + 1733737 * 2 ^ 59
def prefixEnd_1733737 : Nat := 4983230072969 + 3 ^ 40 * 1733737 * 2
def baseEnd_1733737 : Nat := 593493606322792319809463

theorem tailTrace_1733737 : CollatzResearch.WordTrace tailWord_1733737 prefixEnd_1733737 593493606322792319809463 := by
  unfold tailWord_1733737
  simp only [CollatzResearch.WordTrace]
  refine ⟨63234583319974422551087465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42156388879982948367391643 63234583319974422551087465)
  ·
    refine ⟨47425937489980816913315599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63234583319974422551087465 47425937489980816913315599)
    ·
      refine ⟨71138906234971225369973399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47425937489980816913315599 71138906234971225369973399)
      ·
        refine ⟨106708359352456838054960099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71138906234971225369973399 106708359352456838054960099)
        ·
          refine ⟨160062539028685257082440149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106708359352456838054960099 160062539028685257082440149)
          ·
            refine ⟨3751465758484810712869691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 160062539028685257082440149 3751465758484810712869691)
            ·
              refine ⟨5627198637727216069304537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751465758484810712869691 5627198637727216069304537)
              ·
                refine ⟨4220398978295412051978403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627198637727216069304537 4220398978295412051978403)
                ·
                  refine ⟨6330598467443118077967605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220398978295412051978403 6330598467443118077967605)
                  ·
                    refine ⟨593493606322792319809463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6330598467443118077967605 593493606322792319809463)
                    ·
                      rfl

theorem cell22_1733737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_1733737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733737 prefixEnd_1733737 := by exact prefixLift 1733737
  have htrace : WordTrace (prefixWord ++ tailWord_1733737) baseStart_1733737 baseEnd_1733737 := by
    simpa [prefixWord, tailWord_1733737, baseEnd_1733737] using wordTrace_append hprefix tailTrace_1733737
  have hstable : (prefixWord ++ tailWord_1733737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733737).length < 2 ^ (prefixWord ++ tailWord_1733737).sum := by decide
  have hdescent : baseEnd_1733737 < baseStart_1733737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733741 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_1733741 : Nat := 118140960795 + 1733741 * 2 ^ 59
def prefixEnd_1733741 : Nat := 4983230072969 + 3 ^ 40 * 1733741 * 2
def baseEnd_1733741 : Nat := 593494975604537642709451

theorem tailTrace_1733741 : CollatzResearch.WordTrace tailWord_1733741 prefixEnd_1733741 593494975604537642709451 := by
  unfold tailWord_1733741
  simp only [CollatzResearch.WordTrace]
  refine ⟨63234729211959931234233077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42156486141306620822822051 63234729211959931234233077)
  ·
    refine ⟨5928255863621243553209351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63234729211959931234233077 5928255863621243553209351)
    ·
      refine ⟨8892383795431865329814027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5928255863621243553209351 8892383795431865329814027)
      ·
        refine ⟨13338575693147797994721041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8892383795431865329814027 13338575693147797994721041)
        ·
          refine ⟨10003931769860848496040781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13338575693147797994721041 10003931769860848496040781)
          ·
            refine ⟨3751474413697818186015293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10003931769860848496040781 3751474413697818186015293)
            ·
              refine ⟨1406802905136681819755735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3751474413697818186015293 1406802905136681819755735)
              ·
                refine ⟨2110204357705022729633603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406802905136681819755735 2110204357705022729633603)
                ·
                  refine ⟨3165306536557534094450405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110204357705022729633603 3165306536557534094450405)
                  ·
                    refine ⟨593494975604537642709451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165306536557534094450405 593494975604537642709451)
                    ·
                      rfl

theorem cell22_1733741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_1733741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733741 prefixEnd_1733741 := by exact prefixLift 1733741
  have htrace : WordTrace (prefixWord ++ tailWord_1733741) baseStart_1733741 baseEnd_1733741 := by
    simpa [prefixWord, tailWord_1733741, baseEnd_1733741] using wordTrace_append hprefix tailTrace_1733741
  have hstable : (prefixWord ++ tailWord_1733741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733741).length < 2 ^ (prefixWord ++ tailWord_1733741).sum := by decide
  have hdescent : baseEnd_1733741 < baseStart_1733741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733752 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_1733752 : Nat := 118140960795 + 1733752 * 2 ^ 59
def prefixEnd_1733752 : Nat := 4983230072969 + 3 ^ 40 * 1733752 * 2
def baseEnd_1733752 : Nat := 593498741129337280684417

theorem tailTrace_1733752 : CollatzResearch.WordTrace tailWord_1733752 prefixEnd_1733752 593498741129337280684417 := by
  unfold tailWord_1733752
  simp only [CollatzResearch.WordTrace]
  refine ⟨31617565207460040056441755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42156753609946720075255673 31617565207460040056441755)
  ·
    refine ⟨47426347811190060084662633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31617565207460040056441755 47426347811190060084662633)
    ·
      refine ⟨35569760858392545063496975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47426347811190060084662633 35569760858392545063496975)
      ·
        refine ⟨53354641287588817595245463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35569760858392545063496975 53354641287588817595245463)
        ·
          refine ⟨80031961931383226392868195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53354641287588817595245463 80031961931383226392868195)
          ·
            refine ⟨120047942897074839589302293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80031961931383226392868195 120047942897074839589302293)
            ·
              refine ⟨5627247323300383105748545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120047942897074839589302293 5627247323300383105748545)
              ·
                refine ⟨4220435492475287329311409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627247323300383105748545 4220435492475287329311409)
                ·
                  refine ⟨3165326619356465496983557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220435492475287329311409 3165326619356465496983557)
                  ·
                    refine ⟨593498741129337280684417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165326619356465496983557 593498741129337280684417)
                    ·
                      rfl

theorem cell22_1733752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_1733752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733752 prefixEnd_1733752 := by exact prefixLift 1733752
  have htrace : WordTrace (prefixWord ++ tailWord_1733752) baseStart_1733752 baseEnd_1733752 := by
    simpa [prefixWord, tailWord_1733752, baseEnd_1733752] using wordTrace_append hprefix tailTrace_1733752
  have hstable : (prefixWord ++ tailWord_1733752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733752).length < 2 ^ (prefixWord ++ tailWord_1733752).sum := by decide
  have hdescent : baseEnd_1733752 < baseStart_1733752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733784 : List Nat := [2, 1, 2, 4, 2, 2, 3, 6]
def baseStart_1733784 : Nat := 118140960795 + 1733784 * 2 ^ 59
def prefixEnd_1733784 : Nat := 4983230072969 + 3 ^ 40 * 1733784 * 2
def baseEnd_1733784 : Nat := 65945521709255540431591

theorem tailTrace_1733784 : CollatzResearch.WordTrace tailWord_1733784 prefixEnd_1733784 65945521709255540431591 := by
  unfold tailWord_1733784
  simp only [CollatzResearch.WordTrace]
  refine ⟨31618148775402074789024203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42157531700536099718698937 31618148775402074789024203)
  ·
    refine ⟨47427223163103112183536305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31618148775402074789024203 47427223163103112183536305)
    ·
      refine ⟨35570417372327334137652229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47427223163103112183536305 35570417372327334137652229)
      ·
        refine ⟨6669453257311375150809793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35570417372327334137652229 6669453257311375150809793)
        ·
          refine ⟨5002089942983531363107345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6669453257311375150809793 5002089942983531363107345)
          ·
            refine ⟨3751567457237648522330509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5002089942983531363107345 3751567457237648522330509)
            ·
              refine ⟨1406837796464118195873941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3751567457237648522330509 1406837796464118195873941)
              ·
                refine ⟨65945521709255540431591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1406837796464118195873941 65945521709255540431591)
                ·
                  rfl

theorem cell22_1733784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 6].length) (baseStart_1733784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733784 prefixEnd_1733784 := by exact prefixLift 1733784
  have htrace : WordTrace (prefixWord ++ tailWord_1733784) baseStart_1733784 baseEnd_1733784 := by
    simpa [prefixWord, tailWord_1733784, baseEnd_1733784] using wordTrace_append hprefix tailTrace_1733784
  have hstable : (prefixWord ++ tailWord_1733784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733784).length < 2 ^ (prefixWord ++ tailWord_1733784).sum := by decide
  have hdescent : baseEnd_1733784 < baseStart_1733784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733786 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_1733786 : Nat := 118140960795 + 1733786 * 2 ^ 59
def prefixEnd_1733786 : Nat := 4983230072969 + 3 ^ 40 * 1733786 * 2
def baseEnd_1733786 : Nat := 593510380024172525334313

theorem tailTrace_1733786 : CollatzResearch.WordTrace tailWord_1733786 prefixEnd_1733786 593510380024172525334313 := by
  unfold tailWord_1733786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809092624199225979905303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42157580331197935946414141 15809092624199225979905303)
  ·
    refine ⟨23713638936298838969857955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15809092624199225979905303 23713638936298838969857955)
    ·
      refine ⟨35570458404448258454786933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23713638936298838969857955 35570458404448258454786933)
      ·
        refine ⟨3334730475417024230136275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35570458404448258454786933 3334730475417024230136275)
        ·
          refine ⟨5002095713125536345204413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334730475417024230136275 5002095713125536345204413)
          ·
            refine ⟨1875785892422076129451655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5002095713125536345204413 1875785892422076129451655)
            ·
              refine ⟨2813678838633114194177483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875785892422076129451655 2813678838633114194177483)
              ·
                refine ⟨4220518257949671291266225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813678838633114194177483 4220518257949671291266225)
                ·
                  refine ⟨3165388693462253468449669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220518257949671291266225 3165388693462253468449669)
                  ·
                    refine ⟨593510380024172525334313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165388693462253468449669 593510380024172525334313)
                    ·
                      rfl

theorem cell22_1733786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_1733786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733786 prefixEnd_1733786 := by exact prefixLift 1733786
  have htrace : WordTrace (prefixWord ++ tailWord_1733786) baseStart_1733786 baseEnd_1733786 := by
    simpa [prefixWord, tailWord_1733786, baseEnd_1733786] using wordTrace_append hprefix tailTrace_1733786
  have hstable : (prefixWord ++ tailWord_1733786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733786).length < 2 ^ (prefixWord ++ tailWord_1733786).sum := by decide
  have hdescent : baseEnd_1733786 < baseStart_1733786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733805 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1733805 : Nat := 118140960795 + 1733805 * 2 ^ 59
def prefixEnd_1733805 : Nat := 4983230072969 + 3 ^ 40 * 1733805 * 2
def baseEnd_1733805 : Nat := 593516884112462809109255

theorem tailTrace_1733805 : CollatzResearch.WordTrace tailWord_1733805 prefixEnd_1733805 593516884112462809109255 := by
  unfold tailWord_1733805
  simp only [CollatzResearch.WordTrace]
  refine ⟨63237063483728070164562869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42158042322485380109708579 63237063483728070164562869)
  ·
    refine ⟨5928474701599506577927769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63237063483728070164562869 5928474701599506577927769)
    ·
      refine ⟨4446356026199629933445827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5928474701599506577927769 4446356026199629933445827)
      ·
        refine ⟨6669534039299444900168741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446356026199629933445827 6669534039299444900168741)
        ·
          refine ⟨1250537632368645918781639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6669534039299444900168741 1250537632368645918781639)
          ·
            refine ⟨1875806448552968878172459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250537632368645918781639 1875806448552968878172459)
            ·
              refine ⟨2813709672829453317258689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875806448552968878172459 2813709672829453317258689)
              ·
                refine ⟨2110282254622089987944017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2813709672829453317258689 2110282254622089987944017)
                ·
                  refine ⟨1582711690966567490958013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2110282254622089987944017 1582711690966567490958013)
                  ·
                    refine ⟨593516884112462809109255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1582711690966567490958013 593516884112462809109255)
                    ·
                      rfl

theorem cell22_1733805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1733805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733805 prefixEnd_1733805 := by exact prefixLift 1733805
  have htrace : WordTrace (prefixWord ++ tailWord_1733805) baseStart_1733805 baseEnd_1733805 := by
    simpa [prefixWord, tailWord_1733805, baseEnd_1733805] using wordTrace_append hprefix tailTrace_1733805
  have hstable : (prefixWord ++ tailWord_1733805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733805).length < 2 ^ (prefixWord ++ tailWord_1733805).sum := by decide
  have hdescent : baseEnd_1733805 < baseStart_1733805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733919 : List Nat := [1, 1, 2, 4, 5, 9]
def baseStart_1733919 : Nat := 118140960795 + 1733919 * 2 ^ 59
def prefixEnd_1733919 : Nat := 4983230072969 + 3 ^ 40 * 1733919 * 2
def baseEnd_1733919 : Nat := 7327850723977833478505

theorem tailTrace_1733919 : CollatzResearch.WordTrace tailWord_1733919 prefixEnd_1733919 7327850723977833478505 := by
  unfold tailWord_1733919
  simp only [CollatzResearch.WordTrace]
  refine ⟨63241221405315067634212811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42160814270210045089475207 63241221405315067634212811)
  ·
    refine ⟨94861832107972601451319217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63241221405315067634212811 94861832107972601451319217)
    ·
      refine ⟨71146374080979451088489413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94861832107972601451319217 71146374080979451088489413)
      ·
        refine ⟨13339945140183647079091765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71146374080979451088489413 13339945140183647079091765)
        ·
          refine ⟨1250619856892216913664853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13339945140183647079091765 1250619856892216913664853)
          ·
            refine ⟨7327850723977833478505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1250619856892216913664853 7327850723977833478505)
            ·
              rfl

theorem cell22_1733919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 9].length) (baseStart_1733919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733919 prefixEnd_1733919 := by exact prefixLift 1733919
  have htrace : WordTrace (prefixWord ++ tailWord_1733919) baseStart_1733919 baseEnd_1733919 := by
    simpa [prefixWord, tailWord_1733919, baseEnd_1733919] using wordTrace_append hprefix tailTrace_1733919
  have hstable : (prefixWord ++ tailWord_1733919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733919).length < 2 ^ (prefixWord ++ tailWord_1733919).sum := by decide
  have hdescent : baseEnd_1733919 < baseStart_1733919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733951 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 3, 3]
def baseStart_1733951 : Nat := 118140960795 + 1733951 * 2 ^ 59
def prefixEnd_1733951 : Nat := 4983230072969 + 3 ^ 40 * 1733951 * 2
def baseEnd_1733951 : Nat := 593566862896167094958807

theorem tailTrace_1733951 : CollatzResearch.WordTrace tailWord_1733951 prefixEnd_1733951 593566862896167094958807 := by
  unfold tailWord_1733951
  simp only [CollatzResearch.WordTrace]
  refine ⟨63242388541199137099377707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42161592360799424732918471 63242388541199137099377707)
  ·
    refine ⟨94863582811798705649066561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63242388541199137099377707 94863582811798705649066561)
    ·
      refine ⟨71147687108849029236799921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94863582811798705649066561 71147687108849029236799921)
      ·
        refine ⟨53360765331636771927599941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71147687108849029236799921 53360765331636771927599941)
        ·
          refine ⟨10005143499681894736424989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53360765331636771927599941 10005143499681894736424989)
          ·
            refine ⟨3751928812380710526159371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10005143499681894736424989 3751928812380710526159371)
            ·
              refine ⟨5627893218571065789239057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751928812380710526159371 5627893218571065789239057)
              ·
                refine ⟨4220919913928299341929293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627893218571065789239057 4220919913928299341929293)
                ·
                  refine ⟨1582844967723112253223485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4220919913928299341929293 1582844967723112253223485)
                  ·
                    refine ⟨593566862896167094958807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1582844967723112253223485 593566862896167094958807)
                    ·
                      rfl

theorem cell22_1733951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_1733951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733951 prefixEnd_1733951 := by exact prefixLift 1733951
  have htrace : WordTrace (prefixWord ++ tailWord_1733951) baseStart_1733951 baseEnd_1733951 := by
    simpa [prefixWord, tailWord_1733951, baseEnd_1733951] using wordTrace_append hprefix tailTrace_1733951
  have hstable : (prefixWord ++ tailWord_1733951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733951).length < 2 ^ (prefixWord ++ tailWord_1733951).sum := by decide
  have hdescent : baseEnd_1733951 < baseStart_1733951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733968 : List Nat := [2, 1, 1, 1, 1, 5, 4, 3, 1, 3]
def baseStart_1733968 : Nat := 118140960795 + 1733968 * 2 ^ 59
def prefixEnd_1733968 : Nat := 4983230072969 + 3 ^ 40 * 1733968 * 2
def baseEnd_1733968 : Nat := 593572682343584717283755

theorem tailTrace_1733968 : CollatzResearch.WordTrace tailWord_1733968 prefixEnd_1733968 593572682343584717283755 := by
  unfold tailWord_1733968
  simp only [CollatzResearch.WordTrace]
  refine ⟨31621504291068774501373279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42162005721425032668497705 31621504291068774501373279)
  ·
    refine ⟨47432256436603161752059919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31621504291068774501373279 47432256436603161752059919)
    ·
      refine ⟨71148384654904742628089879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47432256436603161752059919 71148384654904742628089879)
      ·
        refine ⟨106722576982357113942134819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71148384654904742628089879 106722576982357113942134819)
        ·
          refine ⟨160083865473535670913202229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106722576982357113942134819 160083865473535670913202229)
          ·
            refine ⟨15007862388143969148112709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160083865473535670913202229 15007862388143969148112709)
            ·
              refine ⟨2813974197776994215271133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15007862388143969148112709 2813974197776994215271133)
              ·
                refine ⟨1055240324166372830726675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2813974197776994215271133 1055240324166372830726675)
                ·
                  refine ⟨1582860486249559246090013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055240324166372830726675 1582860486249559246090013)
                  ·
                    refine ⟨593572682343584717283755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1582860486249559246090013 593572682343584717283755)
                    ·
                      rfl

theorem cell22_1733968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 3].length) (baseStart_1733968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1733968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1733968 prefixEnd_1733968 := by exact prefixLift 1733968
  have htrace : WordTrace (prefixWord ++ tailWord_1733968) baseStart_1733968 baseEnd_1733968 := by
    simpa [prefixWord, tailWord_1733968, baseEnd_1733968] using wordTrace_append hprefix tailTrace_1733968
  have hstable : (prefixWord ++ tailWord_1733968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733968).length < 2 ^ (prefixWord ++ tailWord_1733968).sum := by decide
  have hdescent : baseEnd_1733968 < baseStart_1733968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734009 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 6]
def baseStart_1734009 : Nat := 118140960795 + 1734009 * 2 ^ 59
def prefixEnd_1734009 : Nat := 4983230072969 + 3 ^ 40 * 1734009 * 2
def baseEnd_1734009 : Nat := 197862239160491425669543

theorem tailTrace_1734009 : CollatzResearch.WordTrace tailWord_1734009 prefixEnd_1734009 197862239160491425669543 := by
  unfold tailWord_1734009
  simp only [CollatzResearch.WordTrace]
  refine ⟨63244503974989013004989081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42163002649992675336659387 63244503974989013004989081)
  ·
    refine ⟨47433377981241759753741811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63244503974989013004989081 47433377981241759753741811)
    ·
      refine ⟨71150066971862639630612717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47433377981241759753741811 71150066971862639630612717)
      ·
        refine ⟨26681275114448489861479769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71150066971862639630612717 26681275114448489861479769)
        ·
          refine ⟨20010956335836367396109827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26681275114448489861479769 20010956335836367396109827)
          ·
            refine ⟨30016434503754551094164741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20010956335836367396109827 30016434503754551094164741)
            ·
              refine ⟨5628081469453978330155889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30016434503754551094164741 5628081469453978330155889)
              ·
                refine ⟨4221061102090483747616917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628081469453978330155889 4221061102090483747616917)
                ·
                  refine ⟨197862239160491425669543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4221061102090483747616917 197862239160491425669543)
                  ·
                    rfl

theorem cell22_1734009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_1734009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734009 prefixEnd_1734009 := by exact prefixLift 1734009
  have htrace : WordTrace (prefixWord ++ tailWord_1734009) baseStart_1734009 baseEnd_1734009 := by
    simpa [prefixWord, tailWord_1734009, baseEnd_1734009] using wordTrace_append hprefix tailTrace_1734009
  have hstable : (prefixWord ++ tailWord_1734009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734009).length < 2 ^ (prefixWord ++ tailWord_1734009).sum := by decide
  have hdescent : baseEnd_1734009 < baseStart_1734009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734011 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 1, 4]
def baseStart_1734011 : Nat := 118140960795 + 1734011 * 2 ^ 59
def prefixEnd_1734011 : Nat := 4983230072969 + 3 ^ 40 * 1734011 * 2
def baseEnd_1734011 : Nat := 593587402122346938458623

theorem tailTrace_1734011 : CollatzResearch.WordTrace tailWord_1734011 prefixEnd_1734011 593587402122346938458623 := by
  unfold tailWord_1734011
  simp only [CollatzResearch.WordTrace]
  refine ⟨63244576920981767346561887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42163051280654511564374591 63244576920981767346561887)
  ·
    refine ⟨94866865381472651019842831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63244576920981767346561887 94866865381472651019842831)
    ·
      refine ⟨142300298072208976529764247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94866865381472651019842831 142300298072208976529764247)
      ·
        refine ⟨213450447108313464794646371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142300298072208976529764247 213450447108313464794646371)
        ·
          refine ⟨320175670662470197191969557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213450447108313464794646371 320175670662470197191969557)
          ·
            refine ⟨15008234562303290493373573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 320175670662470197191969557 15008234562303290493373573)
            ·
              refine ⟨2814043980431866967507545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15008234562303290493373573 2814043980431866967507545)
              ·
                refine ⟨2110532985323900225630659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814043980431866967507545 2110532985323900225630659)
                ·
                  refine ⟨3165799477985850338445989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110532985323900225630659 3165799477985850338445989)
                  ·
                    refine ⟨593587402122346938458623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165799477985850338445989 593587402122346938458623)
                    ·
                      rfl

theorem cell22_1734011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 4].length) (baseStart_1734011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734011 prefixEnd_1734011 := by exact prefixLift 1734011
  have htrace : WordTrace (prefixWord ++ tailWord_1734011) baseStart_1734011 baseEnd_1734011 := by
    simpa [prefixWord, tailWord_1734011, baseEnd_1734011] using wordTrace_append hprefix tailTrace_1734011
  have hstable : (prefixWord ++ tailWord_1734011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734011).length < 2 ^ (prefixWord ++ tailWord_1734011).sum := by decide
  have hdescent : baseEnd_1734011 < baseStart_1734011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734041 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 4, 3]
def baseStart_1734041 : Nat := 118140960795 + 1734041 * 2 ^ 59
def prefixEnd_1734041 : Nat := 4983230072969 + 3 ^ 40 * 1734041 * 2
def baseEnd_1734041 : Nat := 593597671735436860208531

theorem tailTrace_1734041 : CollatzResearch.WordTrace tailWord_1734041 prefixEnd_1734041 593597671735436860208531 := by
  unfold tailWord_1734041
  simp only [CollatzResearch.WordTrace]
  refine ⟨63245671110873082470153977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42163780740582054980102651 63245671110873082470153977)
  ·
    refine ⟨47434253333154811852615483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63245671110873082470153977 47434253333154811852615483)
    ·
      refine ⟨71151379999732217778923225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47434253333154811852615483 71151379999732217778923225)
      ·
        refine ⟨53363534999799163334192419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71151379999732217778923225 53363534999799163334192419)
        ·
          refine ⟨80045302499698745001288629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53363534999799163334192419 80045302499698745001288629)
          ·
            refine ⟨7504247109346757343870809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80045302499698745001288629 7504247109346757343870809)
            ·
              refine ⟨5628185332010068007903107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7504247109346757343870809 5628185332010068007903107)
              ·
                refine ⟨8442277998015102011854661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628185332010068007903107 8442277998015102011854661)
                ·
                  refine ⟨1582927124627831627222749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8442277998015102011854661 1582927124627831627222749)
                  ·
                    refine ⟨593597671735436860208531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1582927124627831627222749 593597671735436860208531)
                    ·
                      rfl

theorem cell22_1734041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_1734041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734041 prefixEnd_1734041 := by exact prefixLift 1734041
  have htrace : WordTrace (prefixWord ++ tailWord_1734041) baseStart_1734041 baseEnd_1734041 := by
    simpa [prefixWord, tailWord_1734041, baseEnd_1734041] using wordTrace_append hprefix tailTrace_1734041
  have hstable : (prefixWord ++ tailWord_1734041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734041).length < 2 ^ (prefixWord ++ tailWord_1734041).sum := by decide
  have hdescent : baseEnd_1734041 < baseStart_1734041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734073 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_1734073 : Nat := 118140960795 + 1734073 * 2 ^ 59
def prefixEnd_1734073 : Nat := 4983230072969 + 3 ^ 40 * 1734073 * 2
def baseEnd_1734073 : Nat := 593608625989399443408433

theorem tailTrace_1734073 : CollatzResearch.WordTrace tailWord_1734073 prefixEnd_1734073 593608625989399443408433 := by
  unfold tailWord_1734073
  simp only [CollatzResearch.WordTrace]
  refine ⟨63246838246757151935318873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42164558831171434623545915 63246838246757151935318873)
  ·
    refine ⟨47435128685067863951489155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63246838246757151935318873 47435128685067863951489155)
    ·
      refine ⟨71152693027601795927233733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47435128685067863951489155 71152693027601795927233733)
      ·
        refine ⟨13341129942675336736356325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71152693027601795927233733 13341129942675336736356325)
        ·
          refine ⟨2501461864251625638066811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13341129942675336736356325 2501461864251625638066811)
          ·
            refine ⟨3752192796377438457100217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501461864251625638066811 3752192796377438457100217)
            ·
              refine ⟨2814144597283078842825163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752192796377438457100217 2814144597283078842825163)
              ·
                refine ⟨4221216895924618264237745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814144597283078842825163 4221216895924618264237745)
                ·
                  refine ⟨3165912671943463698178309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221216895924618264237745 3165912671943463698178309)
                  ·
                    refine ⟨593608625989399443408433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165912671943463698178309 593608625989399443408433)
                    ·
                      rfl

theorem cell22_1734073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_1734073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734073 prefixEnd_1734073 := by exact prefixLift 1734073
  have htrace : WordTrace (prefixWord ++ tailWord_1734073) baseStart_1734073 baseEnd_1734073 := by
    simpa [prefixWord, tailWord_1734073, baseEnd_1734073] using wordTrace_append hprefix tailTrace_1734073
  have hstable : (prefixWord ++ tailWord_1734073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734073).length < 2 ^ (prefixWord ++ tailWord_1734073).sum := by decide
  have hdescent : baseEnd_1734073 < baseStart_1734073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734161 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 6]
def baseStart_1734161 : Nat := 118140960795 + 1734161 * 2 ^ 59
def prefixEnd_1734161 : Nat := 4983230072969 + 3 ^ 40 * 1734161 * 2
def baseEnd_1734161 : Nat := 197879583395932182402721

theorem tailTrace_1734161 : CollatzResearch.WordTrace tailWord_1734161 prefixEnd_1734161 197879583395932182402721 := by
  unfold tailWord_1734161
  simp only [CollatzResearch.WordTrace]
  refine ⟨63250047870438342964522337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42166698580292228643014891 63250047870438342964522337)
  ·
    refine ⟨47437535902828757223391753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63250047870438342964522337 47437535902828757223391753)
    ·
      refine ⟨35578151927121567917543815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47437535902828757223391753 35578151927121567917543815)
      ·
        refine ⟨53367227890682351876315723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35578151927121567917543815 53367227890682351876315723)
        ·
          refine ⟨80050841836023527814473585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53367227890682351876315723 80050841836023527814473585)
          ·
            refine ⟨60038131377017645860855189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80050841836023527814473585 60038131377017645860855189)
            ·
              refine ⟨2814287408297702149727587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60038131377017645860855189 2814287408297702149727587)
              ·
                refine ⟨4221431112446553224591381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814287408297702149727587 4221431112446553224591381)
                ·
                  refine ⟨197879583395932182402721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4221431112446553224591381 197879583395932182402721)
                  ·
                    rfl

theorem cell22_1734161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_1734161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734161 prefixEnd_1734161 := by exact prefixLift 1734161
  have htrace : WordTrace (prefixWord ++ tailWord_1734161) baseStart_1734161 baseEnd_1734161 := by
    simpa [prefixWord, tailWord_1734161, baseEnd_1734161] using wordTrace_append hprefix tailTrace_1734161
  have hstable : (prefixWord ++ tailWord_1734161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734161).length < 2 ^ (prefixWord ++ tailWord_1734161).sum := by decide
  have hdescent : baseEnd_1734161 < baseStart_1734161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734195 : List Nat := [1, 1, 1, 2, 4, 5, 1, 3, 4]
def baseStart_1734195 : Nat := 118140960795 + 1734195 * 2 ^ 59
def prefixEnd_1734195 : Nat := 4983230072969 + 3 ^ 40 * 1734195 * 2
def baseEnd_1734195 : Nat := 197883463027543930619353

theorem tailTrace_1734195 : CollatzResearch.WordTrace tailWord_1734195 prefixEnd_1734195 197883463027543930619353 := by
  unfold tailWord_1734195
  simp only [CollatzResearch.WordTrace]
  refine ⟨63251287952315166771260039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42167525301543444514173359 63251287952315166771260039)
  ·
    refine ⟨94876931928472750156890059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63251287952315166771260039 94876931928472750156890059)
    ·
      refine ⟨142315397892709125235335089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94876931928472750156890059 142315397892709125235335089)
      ·
        refine ⟨106736548419531843926501317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142315397892709125235335089 106736548419531843926501317)
        ·
          refine ⟨20013102828662220736218997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106736548419531843926501317 20013102828662220736218997)
          ·
            refine ⟨1876228390187083194020531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20013102828662220736218997 1876228390187083194020531)
            ·
              refine ⟨2814342585280624791030797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876228390187083194020531 2814342585280624791030797)
              ·
                refine ⟨1055378469480234296636549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2814342585280624791030797 1055378469480234296636549)
                ·
                  refine ⟨197883463027543930619353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055378469480234296636549 197883463027543930619353)
                  ·
                    rfl

theorem cell22_1734195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 4].length) (baseStart_1734195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734195 prefixEnd_1734195 := by exact prefixLift 1734195
  have htrace : WordTrace (prefixWord ++ tailWord_1734195) baseStart_1734195 baseEnd_1734195 := by
    simpa [prefixWord, tailWord_1734195, baseEnd_1734195] using wordTrace_append hprefix tailTrace_1734195
  have hstable : (prefixWord ++ tailWord_1734195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734195).length < 2 ^ (prefixWord ++ tailWord_1734195).sum := by decide
  have hdescent : baseEnd_1734195 < baseStart_1734195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734255 : List Nat := [1, 1, 2, 1, 3, 2, 1, 7, 1, 3]
def baseStart_1734255 : Nat := 118140960795 + 1734255 * 2 ^ 59
def prefixEnd_1734255 : Nat := 4983230072969 + 3 ^ 40 * 1734255 * 2
def baseEnd_1734255 : Nat := 593670928308811635357875

theorem tailTrace_1734255 : CollatzResearch.WordTrace tailWord_1734255 prefixEnd_1734255 593670928308811635357875 := by
  unfold tailWord_1734255
  simp only [CollatzResearch.WordTrace]
  refine ⟨63253476332097797018444219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42168984221398531345629479 63253476332097797018444219)
  ·
    refine ⟨94880214498146695527666329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63253476332097797018444219 94880214498146695527666329)
    ·
      refine ⟨71160160873610021645749747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94880214498146695527666329 71160160873610021645749747)
      ·
        refine ⟨106740241310415032468624621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71160160873610021645749747 106740241310415032468624621)
        ·
          refine ⟨40027590491405637175734233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106740241310415032468624621 40027590491405637175734233)
          ·
            refine ⟨30020692868554227881800675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40027590491405637175734233 30020692868554227881800675)
            ·
              refine ⟨45031039302831341822701013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30020692868554227881800675 45031039302831341822701013)
              ·
                refine ⟨1055414983660109573969555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45031039302831341822701013 1055414983660109573969555)
                ·
                  refine ⟨1583122475490164360954333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055414983660109573969555 1583122475490164360954333)
                  ·
                    refine ⟨593670928308811635357875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583122475490164360954333 593670928308811635357875)
                    ·
                      rfl

theorem cell22_1734255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 3].length) (baseStart_1734255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734255 prefixEnd_1734255 := by exact prefixLift 1734255
  have htrace : WordTrace (prefixWord ++ tailWord_1734255) baseStart_1734255 baseEnd_1734255 := by
    simpa [prefixWord, tailWord_1734255, baseEnd_1734255] using wordTrace_append hprefix tailTrace_1734255
  have hstable : (prefixWord ++ tailWord_1734255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734255).length < 2 ^ (prefixWord ++ tailWord_1734255).sum := by decide
  have hdescent : baseEnd_1734255 < baseStart_1734255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734306 : List Nat := [3, 3, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_1734306 : Nat := 118140960795 + 1734306 * 2 ^ 59
def prefixEnd_1734306 : Nat := 4983230072969 + 3 ^ 40 * 1734306 * 2
def baseEnd_1734306 : Nat := 593688386651064502332719

theorem tailTrace_1734306 : CollatzResearch.WordTrace tailWord_1734306 prefixEnd_1734306 593688386651064502332719 := by
  unfold tailWord_1734306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813834113728258182137693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42170224303275355152367181 15813834113728258182137693)
  ·
    refine ⟨5930187792648096818301635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15813834113728258182137693 5930187792648096818301635)
    ·
      refine ⟨8895281688972145227452453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5930187792648096818301635 8895281688972145227452453)
      ·
        refine ⟨1667865316682277230147335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8895281688972145227452453 1667865316682277230147335)
        ·
          refine ⟨2501797975023415845221003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667865316682277230147335 2501797975023415845221003)
          ·
            refine ⟨3752696962535123767831505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501797975023415845221003 3752696962535123767831505)
            ·
              refine ⟨2814522721901342825873629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752696962535123767831505 2814522721901342825873629)
              ·
                refine ⟨1055446020713003559702611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2814522721901342825873629 1055446020713003559702611)
                ·
                  refine ⟨1583169031069505339553917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055446020713003559702611 1583169031069505339553917)
                  ·
                    refine ⟨593688386651064502332719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583169031069505339553917 593688386651064502332719)
                    ·
                      rfl

theorem cell22_1734306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_1734306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734306 prefixEnd_1734306 := by exact prefixLift 1734306
  have htrace : WordTrace (prefixWord ++ tailWord_1734306) baseStart_1734306 baseEnd_1734306 := by
    simpa [prefixWord, tailWord_1734306, baseEnd_1734306] using wordTrace_append hprefix tailTrace_1734306
  have hstable : (prefixWord ++ tailWord_1734306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734306).length < 2 ^ (prefixWord ++ tailWord_1734306).sum := by decide
  have hdescent : baseEnd_1734306 < baseStart_1734306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734330 : List Nat := [3, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_1734330 : Nat := 118140960795 + 1734330 * 2 ^ 59
def prefixEnd_1734330 : Nat := 4983230072969 + 3 ^ 40 * 1734330 * 2
def baseEnd_1734330 : Nat := 197898867447178813244215

theorem tailTrace_1734330 : CollatzResearch.WordTrace tailWord_1734330 prefixEnd_1734330 197898867447178813244215 := by
  unfold tailWord_1734330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814052951706521206856111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42170807871217389884949629 15814052951706521206856111)
  ·
    refine ⟨23721079427559781810284167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15814052951706521206856111 23721079427559781810284167)
    ·
      refine ⟨35581619141339672715426251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23721079427559781810284167 35581619141339672715426251)
      ·
        refine ⟨53372428712009509073139377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35581619141339672715426251 53372428712009509073139377)
        ·
          refine ⟨40029321534007131804854533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53372428712009509073139377 40029321534007131804854533)
          ·
            refine ⟨7505497787626337213410225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40029321534007131804854533 7505497787626337213410225)
            ·
              refine ⟨5629123340719752910057669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7505497787626337213410225 5629123340719752910057669)
              ·
                refine ⟨1055460626384953670635813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5629123340719752910057669 1055460626384953670635813)
                ·
                  refine ⟨197898867447178813244215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055460626384953670635813 197898867447178813244215)
                  ·
                    rfl

theorem cell22_1734330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_1734330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734330 prefixEnd_1734330 := by exact prefixLift 1734330
  have htrace : WordTrace (prefixWord ++ tailWord_1734330) baseStart_1734330 baseEnd_1734330 := by
    simpa [prefixWord, tailWord_1734330, baseEnd_1734330] using wordTrace_append hprefix tailTrace_1734330
  have hstable : (prefixWord ++ tailWord_1734330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734330).length < 2 ^ (prefixWord ++ tailWord_1734330).sum := by decide
  have hdescent : baseEnd_1734330 < baseStart_1734330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734349 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1734349 : Nat := 118140960795 + 1734349 * 2 ^ 59
def prefixEnd_1734349 : Nat := 4983230072969 + 3 ^ 40 * 1734349 * 2
def baseEnd_1734349 : Nat := 593703106429826723507587

theorem tailTrace_1734349 : CollatzResearch.WordTrace tailWord_1734349 prefixEnd_1734349 593703106429826723507587 := by
  unfold tailWord_1734349
  simp only [CollatzResearch.WordTrace]
  refine ⟨63256904793757251072366101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42171269862504834048244067 63256904793757251072366101)
  ·
    refine ⟨2965167412207371144017161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63256904793757251072366101 2965167412207371144017161)
    ·
      refine ⟨2223875559155528358012871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2965167412207371144017161 2223875559155528358012871)
      ·
        refine ⟨3335813338733292537019307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223875559155528358012871 3335813338733292537019307)
        ·
          refine ⟨5003720008099938805528961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335813338733292537019307 5003720008099938805528961)
          ·
            refine ⟨3752790006074954104146721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5003720008099938805528961 3752790006074954104146721)
            ·
              refine ⟨2814592504556215578110041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752790006074954104146721 2814592504556215578110041)
              ·
                refine ⟨2110944378417161683582531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814592504556215578110041 2110944378417161683582531)
                ·
                  refine ⟨3166416567625742525373797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110944378417161683582531 3166416567625742525373797)
                  ·
                    refine ⟨593703106429826723507587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166416567625742525373797 593703106429826723507587)
                    ·
                      rfl

theorem cell22_1734349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1734349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734349 prefixEnd_1734349 := by exact prefixLift 1734349
  have htrace : WordTrace (prefixWord ++ tailWord_1734349) baseStart_1734349 baseEnd_1734349 := by
    simpa [prefixWord, tailWord_1734349, baseEnd_1734349] using wordTrace_append hprefix tailTrace_1734349
  have hstable : (prefixWord ++ tailWord_1734349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734349).length < 2 ^ (prefixWord ++ tailWord_1734349).sum := by decide
  have hdescent : baseEnd_1734349 < baseStart_1734349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734450 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1734450 : Nat := 118140960795 + 1734450 * 2 ^ 59
def prefixEnd_1734450 : Nat := 4983230072969 + 3 ^ 40 * 1734450 * 2
def baseEnd_1734450 : Nat := 593737680793896126732277

theorem tailTrace_1734450 : CollatzResearch.WordTrace tailWord_1734450 prefixEnd_1734450 593737680793896126732277 := by
  unfold tailWord_1734450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815147141597836330448201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42173725710927563547861869 15815147141597836330448201)
  ·
    refine ⟨11861360356198377247836151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15815147141597836330448201 11861360356198377247836151)
    ·
      refine ⟨17792040534297565871754227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11861360356198377247836151 17792040534297565871754227)
      ·
        refine ⟨26688060801446348807631341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17792040534297565871754227 26688060801446348807631341)
        ·
          refine ⟨10008022800542380802861753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26688060801446348807631341 10008022800542380802861753)
          ·
            refine ⟨7506017100406785602146315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10008022800542380802861753 7506017100406785602146315)
            ·
              refine ⟨11259025650610178403219473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7506017100406785602146315 11259025650610178403219473)
              ·
                refine ⟨8444269237957633802414605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11259025650610178403219473 8444269237957633802414605)
                ·
                  refine ⟨3166600964234112675905477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8444269237957633802414605 3166600964234112675905477)
                  ·
                    refine ⟨593737680793896126732277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166600964234112675905477 593737680793896126732277)
                    ·
                      rfl

theorem cell22_1734450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1734450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734450 prefixEnd_1734450 := by exact prefixLift 1734450
  have htrace : WordTrace (prefixWord ++ tailWord_1734450) baseStart_1734450 baseEnd_1734450 := by
    simpa [prefixWord, tailWord_1734450, baseEnd_1734450] using wordTrace_append hprefix tailTrace_1734450
  have hstable : (prefixWord ++ tailWord_1734450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734450).length < 2 ^ (prefixWord ++ tailWord_1734450).sum := by decide
  have hdescent : baseEnd_1734450 < baseStart_1734450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734452 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1734452 : Nat := 118140960795 + 1734452 * 2 ^ 59
def prefixEnd_1734452 : Nat := 4983230072969 + 3 ^ 40 * 1734452 * 2
def baseEnd_1734452 : Nat := 593738365434768788182271

theorem tailTrace_1734452 : CollatzResearch.WordTrace tailWord_1734452 prefixEnd_1734452 593738365434768788182271 := by
  unfold tailWord_1734452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31630330756192049831682805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42173774341589399775577073 31630330756192049831682805)
  ·
    refine ⟨2965343508393004671720263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31630330756192049831682805 2965343508393004671720263)
    ·
      refine ⟨4448015262589507007580395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2965343508393004671720263 4448015262589507007580395)
      ·
        refine ⟨6672022893884260511370593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448015262589507007580395 6672022893884260511370593)
        ·
          refine ⟨5004017170413195383527945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672022893884260511370593 5004017170413195383527945)
          ·
            refine ⟨3753012877809896537645959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5004017170413195383527945 3753012877809896537645959)
            ·
              refine ⟨5629519316714844806468939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753012877809896537645959 5629519316714844806468939)
              ·
                refine ⟨8444278975072267209703409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629519316714844806468939 8444278975072267209703409)
                ·
                  refine ⟨6333209231304200407277557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8444278975072267209703409 6333209231304200407277557)
                  ·
                    refine ⟨593738365434768788182271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6333209231304200407277557 593738365434768788182271)
                    ·
                      rfl

theorem cell22_1734452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1734452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734452 prefixEnd_1734452 := by exact prefixLift 1734452
  have htrace : WordTrace (prefixWord ++ tailWord_1734452) baseStart_1734452 baseEnd_1734452 := by
    simpa [prefixWord, tailWord_1734452, baseEnd_1734452] using wordTrace_append hprefix tailTrace_1734452
  have hstable : (prefixWord ++ tailWord_1734452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734452).length < 2 ^ (prefixWord ++ tailWord_1734452).sum := by decide
  have hdescent : baseEnd_1734452 < baseStart_1734452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734480 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 4, 3]
def baseStart_1734480 : Nat := 118140960795 + 1734480 * 2 ^ 59
def prefixEnd_1734480 : Nat := 4983230072969 + 3 ^ 40 * 1734480 * 2
def baseEnd_1734480 : Nat := 593747950406986048482185

theorem tailTrace_1734480 : CollatzResearch.WordTrace tailWord_1734480 prefixEnd_1734480 593747950406986048482185 := by
  unfold tailWord_1734480
  simp only [CollatzResearch.WordTrace]
  refine ⟨31630841378141330222692447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42174455170855106963589929 31630841378141330222692447)
  ·
    refine ⟨47446262067211995334038671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31630841378141330222692447 47446262067211995334038671)
    ·
      refine ⟨71169393100817993001058007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47446262067211995334038671 71169393100817993001058007)
      ·
        refine ⟨106754089651226989501587011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71169393100817993001058007 106754089651226989501587011)
        ·
          refine ⟨160131134476840484252380517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106754089651226989501587011 160131134476840484252380517)
          ·
            refine ⟨30024587714407590797321347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160131134476840484252380517 30024587714407590797321347)
            ·
              refine ⟨45036881571611386195982021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30024587714407590797321347 45036881571611386195982021)
              ·
                refine ⟨8444415294677134911746629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45036881571611386195982021 8444415294677134911746629)
                ·
                  refine ⟨1583327867751962795952493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8444415294677134911746629 1583327867751962795952493)
                  ·
                    refine ⟨593747950406986048482185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583327867751962795952493 593747950406986048482185)
                    ·
                      rfl

theorem cell22_1734480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_1734480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734480 prefixEnd_1734480 := by exact prefixLift 1734480
  have htrace : WordTrace (prefixWord ++ tailWord_1734480) baseStart_1734480 baseEnd_1734480 := by
    simpa [prefixWord, tailWord_1734480, baseEnd_1734480] using wordTrace_append hprefix tailTrace_1734480
  have hstable : (prefixWord ++ tailWord_1734480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734480).length < 2 ^ (prefixWord ++ tailWord_1734480).sum := by decide
  have hdescent : baseEnd_1734480 < baseStart_1734480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734482 : List Nat := [3, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1734482 : Nat := 118140960795 + 1734482 * 2 ^ 59
def prefixEnd_1734482 : Nat := 4983230072969 + 3 ^ 40 * 1734482 * 2
def baseEnd_1734482 : Nat := 197916211682619569977393

theorem tailTrace_1734482 : CollatzResearch.WordTrace tailWord_1734482 prefixEnd_1734482 197916211682619569977393 := by
  unfold tailWord_1734482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815438925568853696739425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42174503801516943191305133 15815438925568853696739425)
  ·
    refine ⟨11861579194176640272554569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15815438925568853696739425 11861579194176640272554569)
    ·
      refine ⟨8896184395632480204415927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11861579194176640272554569 8896184395632480204415927)
      ·
        refine ⟨13344276593448720306623891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8896184395632480204415927 13344276593448720306623891)
        ·
          refine ⟨20016414890173080459935837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13344276593448720306623891 20016414890173080459935837)
          ·
            refine ⟨7506155583814905172475939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20016414890173080459935837 7506155583814905172475939)
            ·
              refine ⟨11259233375722357758713909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7506155583814905172475939 11259233375722357758713909)
              ·
                refine ⟨1055553128973971039879429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11259233375722357758713909 1055553128973971039879429)
                ·
                  refine ⟨197916211682619569977393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055553128973971039879429 197916211682619569977393)
                  ·
                    rfl

theorem cell22_1734482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1734482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734482 prefixEnd_1734482 := by exact prefixLift 1734482
  have htrace : WordTrace (prefixWord ++ tailWord_1734482) baseStart_1734482 baseEnd_1734482 := by
    simpa [prefixWord, tailWord_1734482, baseEnd_1734482] using wordTrace_append hprefix tailTrace_1734482
  have hstable : (prefixWord ++ tailWord_1734482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734482).length < 2 ^ (prefixWord ++ tailWord_1734482).sum := by decide
  have hdescent : baseEnd_1734482 < baseStart_1734482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734484 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_1734484 : Nat := 118140960795 + 1734484 * 2 ^ 59
def prefixEnd_1734484 : Nat := 4983230072969 + 3 ^ 40 * 1734484 * 2
def baseEnd_1734484 : Nat := 593749319688731371382173

theorem tailTrace_1734484 : CollatzResearch.WordTrace tailWord_1734484 prefixEnd_1734484 593749319688731371382173 := by
  unfold tailWord_1734484
  simp only [CollatzResearch.WordTrace]
  refine ⟨31630914324134084564265253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42174552432178779419020337 31630914324134084564265253)
  ·
    refine ⟨5930796435775140855799735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31630914324134084564265253 5930796435775140855799735)
    ·
      refine ⟨8896194653662711283699603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5930796435775140855799735 8896194653662711283699603)
      ·
        refine ⟨13344291980494066925549405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8896194653662711283699603 13344291980494066925549405)
        ·
          refine ⟨5004109492685275097081027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13344291980494066925549405 5004109492685275097081027)
          ·
            refine ⟨7506164239027912645621541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004109492685275097081027 7506164239027912645621541)
            ·
              refine ⟨1407405794817733621054039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7506164239027912645621541 1407405794817733621054039)
              ·
                refine ⟨2111108692226600431581059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407405794817733621054039 2111108692226600431581059)
                ·
                  refine ⟨3166663038339900647371589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111108692226600431581059 3166663038339900647371589)
                  ·
                    refine ⟨593749319688731371382173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166663038339900647371589 593749319688731371382173)
                    ·
                      rfl

theorem cell22_1734484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_1734484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734484 prefixEnd_1734484 := by exact prefixLift 1734484
  have htrace : WordTrace (prefixWord ++ tailWord_1734484) baseStart_1734484 baseEnd_1734484 := by
    simpa [prefixWord, tailWord_1734484, baseEnd_1734484] using wordTrace_append hprefix tailTrace_1734484
  have hstable : (prefixWord ++ tailWord_1734484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734484).length < 2 ^ (prefixWord ++ tailWord_1734484).sum := by decide
  have hdescent : baseEnd_1734484 < baseStart_1734484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734550 : List Nat := [5, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1734550 : Nat := 118140960795 + 1734550 * 2 ^ 59
def prefixEnd_1734550 : Nat := 4983230072969 + 3 ^ 40 * 1734550 * 2
def baseEnd_1734550 : Nat := 197923970945843066410657

theorem tailTrace_1734550 : CollatzResearch.WordTrace tailWord_1734550 prefixEnd_1734550 197923970945843066410657 := by
  unfold tailWord_1734550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954014741626816400027069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42176157244019374933622069 3954014741626816400027069)
  ·
    refine ⟨1482755528110056150010151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3954014741626816400027069 1482755528110056150010151)
    ·
      refine ⟨2224133292165084225015227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482755528110056150010151 2224133292165084225015227)
      ·
        refine ⟨3336199938247626337522841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224133292165084225015227 3336199938247626337522841)
        ·
          refine ⟨2502149953685719753142131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336199938247626337522841 2502149953685719753142131)
          ·
            refine ⟨3753224930528579629713197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502149953685719753142131 3753224930528579629713197)
            ·
              refine ⟨1407459348948217361142449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3753224930528579629713197 1407459348948217361142449)
              ·
                refine ⟨1055594511711163020856837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407459348948217361142449 1055594511711163020856837)
                ·
                  refine ⟨197923970945843066410657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055594511711163020856837 197923970945843066410657)
                  ·
                    rfl

theorem cell22_1734550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1734550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734550 prefixEnd_1734550 := by exact prefixLift 1734550
  have htrace : WordTrace (prefixWord ++ tailWord_1734550) baseStart_1734550 baseEnd_1734550 := by
    simpa [prefixWord, tailWord_1734550, baseEnd_1734550] using wordTrace_append hprefix tailTrace_1734550
  have hstable : (prefixWord ++ tailWord_1734550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734550).length < 2 ^ (prefixWord ++ tailWord_1734550).sum := by decide
  have hdescent : baseEnd_1734550 < baseStart_1734550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734602 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_1734602 : Nat := 118140960795 + 1734602 * 2 ^ 59
def prefixEnd_1734602 : Nat := 4983230072969 + 3 ^ 40 * 1734602 * 2
def baseEnd_1734602 : Nat := 593789713500218396931811

theorem tailTrace_1734602 : CollatzResearch.WordTrace tailWord_1734602 prefixEnd_1734602 593789713500218396931811 := by
  unfold tailWord_1734602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15816533115460168820331515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42177421641227116854217373 15816533115460168820331515)
  ·
    refine ⟨23724799673190253230497273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15816533115460168820331515 23724799673190253230497273)
    ·
      refine ⟨17793599754892689922872955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23724799673190253230497273 17793599754892689922872955)
      ·
        refine ⟨26690399632339034884309433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17793599754892689922872955 26690399632339034884309433)
        ·
          refine ⟨20017799724254276163232075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26690399632339034884309433 20017799724254276163232075)
          ·
            refine ⟨30026699586381414244848113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20017799724254276163232075 30026699586381414244848113)
            ·
              refine ⟨22520024689786060683636085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30026699586381414244848113 22520024689786060683636085)
              ·
                refine ⟨2111252314667443189090883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22520024689786060683636085 2111252314667443189090883)
                ·
                  refine ⟨3166878472001164783636325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111252314667443189090883 3166878472001164783636325)
                  ·
                    refine ⟨593789713500218396931811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166878472001164783636325 593789713500218396931811)
                    ·
                      rfl

theorem cell22_1734602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_1734602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734602 prefixEnd_1734602 := by exact prefixLift 1734602
  have htrace : WordTrace (prefixWord ++ tailWord_1734602) baseStart_1734602 baseEnd_1734602 := by
    simpa [prefixWord, tailWord_1734602, baseEnd_1734602] using wordTrace_append hprefix tailTrace_1734602
  have hstable : (prefixWord ++ tailWord_1734602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734602).length < 2 ^ (prefixWord ++ tailWord_1734602).sum := by decide
  have hdescent : baseEnd_1734602 < baseStart_1734602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734610 : List Nat := [3, 2, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1734610 : Nat := 118140960795 + 1734610 * 2 ^ 59
def prefixEnd_1734610 : Nat := 4983230072969 + 3 ^ 40 * 1734610 * 2
def baseEnd_1734610 : Nat := 593792452063709042731787

theorem tailTrace_1734610 : CollatzResearch.WordTrace tailWord_1734610 prefixEnd_1734610 593792452063709042731787 := by
  unfold tailWord_1734610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15816606061452923161904321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42177616163874461765078189 15816606061452923161904321)
  ·
    refine ⟨11862454546089692371428241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15816606061452923161904321 11862454546089692371428241)
    ·
      refine ⟨8896840909567269278571181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11862454546089692371428241 8896840909567269278571181)
      ·
        refine ⟨3336315341087725979464193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8896840909567269278571181 3336315341087725979464193)
        ·
          refine ⟨2502236505815794484598145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336315341087725979464193 2502236505815794484598145)
          ·
            refine ⟨1876677379361845863448609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502236505815794484598145 1876677379361845863448609)
            ·
              refine ⟨1407508034521384397586457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1876677379361845863448609 1407508034521384397586457)
              ·
                refine ⟨1055631025891038298189843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407508034521384397586457 1055631025891038298189843)
                ·
                  refine ⟨1583446538836557447284765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055631025891038298189843 1583446538836557447284765)
                  ·
                    refine ⟨593792452063709042731787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583446538836557447284765 593792452063709042731787)
                    ·
                      rfl

theorem cell22_1734610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1734610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734610 prefixEnd_1734610 := by exact prefixLift 1734610
  have htrace : WordTrace (prefixWord ++ tailWord_1734610) baseStart_1734610 baseEnd_1734610 := by
    simpa [prefixWord, tailWord_1734610, baseEnd_1734610] using wordTrace_append hprefix tailTrace_1734610
  have hstable : (prefixWord ++ tailWord_1734610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734610).length < 2 ^ (prefixWord ++ tailWord_1734610).sum := by decide
  have hdescent : baseEnd_1734610 < baseStart_1734610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734615 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1734615 : Nat := 118140960795 + 1734615 * 2 ^ 59
def prefixEnd_1734615 : Nat := 4983230072969 + 3 ^ 40 * 1734615 * 2
def baseEnd_1734615 : Nat := 593794163665890696356771

theorem tailTrace_1734615 : CollatzResearch.WordTrace tailWord_1734615 prefixEnd_1734615 593794163665890696356771 := by
  unfold tailWord_1734615
  simp only [CollatzResearch.WordTrace]
  refine ⟨63266606610793578501549299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42177737740529052334366199 63266606610793578501549299)
  ·
    refine ⟨94899909916190367752323949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63266606610793578501549299 94899909916190367752323949)
    ·
      refine ⟨35587466218571387907121481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94899909916190367752323949 35587466218571387907121481)
      ·
        refine ⟨26690599663928540930341111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35587466218571387907121481 26690599663928540930341111)
        ·
          refine ⟨40035899495892811395511667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26690599663928540930341111 40035899495892811395511667)
          ·
            refine ⟨60053849243839217093267501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40035899495892811395511667 60053849243839217093267501)
            ·
              refine ⟨22520193466439706409975313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60053849243839217093267501 22520193466439706409975313)
              ·
                refine ⟨16890145099829779807481485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22520193466439706409975313 16890145099829779807481485)
                ·
                  refine ⟨6333804412436167427805557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16890145099829779807481485 6333804412436167427805557)
                  ·
                    refine ⟨593794163665890696356771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6333804412436167427805557 593794163665890696356771)
                    ·
                      rfl

theorem cell22_1734615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1734615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734615 prefixEnd_1734615 := by exact prefixLift 1734615
  have htrace : WordTrace (prefixWord ++ tailWord_1734615) baseStart_1734615 baseEnd_1734615 := by
    simpa [prefixWord, tailWord_1734615, baseEnd_1734615] using wordTrace_append hprefix tailTrace_1734615
  have hstable : (prefixWord ++ tailWord_1734615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734615).length < 2 ^ (prefixWord ++ tailWord_1734615).sum := by decide
  have hdescent : baseEnd_1734615 < baseStart_1734615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734632 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1734632 : Nat := 118140960795 + 1734632 * 2 ^ 59
def prefixEnd_1734632 : Nat := 4983230072969 + 3 ^ 40 * 1734632 * 2
def baseEnd_1734632 : Nat := 593799983113308318681719

theorem tailTrace_1734632 : CollatzResearch.WordTrace tailWord_1734632 prefixEnd_1734632 593799983113308318681719 := by
  unfold tailWord_1734632
  simp only [CollatzResearch.WordTrace]
  refine ⟨31633613325865995202459075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42178151101154660269945433 31633613325865995202459075)
  ·
    refine ⟨47450419988798992803688613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31633613325865995202459075 47450419988798992803688613)
    ·
      refine ⟨8896953747899811150691615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47450419988798992803688613 8896953747899811150691615)
      ·
        refine ⟨13345430621849716726037423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8896953747899811150691615 13345430621849716726037423)
        ·
          refine ⟨20018145932774575089056135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13345430621849716726037423 20018145932774575089056135)
          ·
            refine ⟨30027218899161862633584203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20018145932774575089056135 30027218899161862633584203)
            ·
              refine ⟨45040828348742793950376305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30027218899161862633584203 45040828348742793950376305)
              ·
                refine ⟨33780621261557095462782229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45040828348742793950376305 33780621261557095462782229)
                ·
                  refine ⟨1583466621635488849817917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33780621261557095462782229 1583466621635488849817917)
                  ·
                    refine ⟨593799983113308318681719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583466621635488849817917 593799983113308318681719)
                    ·
                      rfl

theorem cell22_1734632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1734632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734632 prefixEnd_1734632 := by exact prefixLift 1734632
  have htrace : WordTrace (prefixWord ++ tailWord_1734632) baseStart_1734632 baseEnd_1734632 := by
    simpa [prefixWord, tailWord_1734632, baseEnd_1734632] using wordTrace_append hprefix tailTrace_1734632
  have hstable : (prefixWord ++ tailWord_1734632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734632).length < 2 ^ (prefixWord ++ tailWord_1734632).sum := by decide
  have hdescent : baseEnd_1734632 < baseStart_1734632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734675 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 8]
def baseStart_1734675 : Nat := 118140960795 + 1734675 * 2 ^ 59
def prefixEnd_1734675 : Nat := 4983230072969 + 3 ^ 40 * 1734675 * 2
def baseEnd_1734675 : Nat := 593814702892070539856587

theorem tailTrace_1734675 : CollatzResearch.WordTrace tailWord_1734675 prefixEnd_1734675 593814702892070539856587 := by
  unfold tailWord_1734675
  simp only [CollatzResearch.WordTrace]
  refine ⟨63268794990576208748733479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42179196660384139165822319 63268794990576208748733479)
  ·
    refine ⟨94903192485864313123100219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63268794990576208748733479 94903192485864313123100219)
    ·
      refine ⟨142354788728796469684650329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94903192485864313123100219 142354788728796469684650329)
      ·
        refine ⟨106766091546597352263487747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142354788728796469684650329 106766091546597352263487747)
        ·
          refine ⟨160149137319896028395231621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106766091546597352263487747 160149137319896028395231621)
          ·
            refine ⟨30027963247480505324105929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160149137319896028395231621 30027963247480505324105929)
            ·
              refine ⟨22520972435610378993079447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30027963247480505324105929 22520972435610378993079447)
              ·
                refine ⟨33781458653415568489619171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22520972435610378993079447 33781458653415568489619171)
                ·
                  refine ⟨50672187980123352734428757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33781458653415568489619171 50672187980123352734428757)
                  ·
                    refine ⟨593814702892070539856587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50672187980123352734428757 593814702892070539856587)
                    ·
                      rfl

theorem cell22_1734675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_1734675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734675 prefixEnd_1734675 := by exact prefixLift 1734675
  have htrace : WordTrace (prefixWord ++ tailWord_1734675) baseStart_1734675 baseEnd_1734675 := by
    simpa [prefixWord, tailWord_1734675, baseEnd_1734675] using wordTrace_append hprefix tailTrace_1734675
  have hstable : (prefixWord ++ tailWord_1734675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734675).length < 2 ^ (prefixWord ++ tailWord_1734675).sum := by decide
  have hdescent : baseEnd_1734675 < baseStart_1734675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734711 : List Nat := [1, 1, 3, 1, 2, 2, 5, 3, 1, 3]
def baseStart_1734711 : Nat := 118140960795 + 1734711 * 2 ^ 59
def prefixEnd_1734711 : Nat := 4983230072969 + 3 ^ 40 * 1734711 * 2
def baseEnd_1734711 : Nat := 593827026427778445956477

theorem tailTrace_1734711 : CollatzResearch.WordTrace tailWord_1734711 prefixEnd_1734711 593827026427778445956477 := by
  unfold tailWord_1734711
  simp only [CollatzResearch.WordTrace]
  refine ⟨63270108018445786897043987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42180072012297191264695991 63270108018445786897043987)
  ·
    refine ⟨94905162027668680345565981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63270108018445786897043987 94905162027668680345565981)
    ·
      refine ⟨35589435760375755129587243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94905162027668680345565981 35589435760375755129587243)
      ·
        refine ⟨53384153640563632694380865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35589435760375755129587243 53384153640563632694380865)
        ·
          refine ⟨40038115230422724520785649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53384153640563632694380865 40038115230422724520785649)
          ·
            refine ⟨30028586422817043390589237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40038115230422724520785649 30028586422817043390589237)
            ·
              refine ⟨2815179977139097817867741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30028586422817043390589237 2815179977139097817867741)
              ·
                refine ⟨1055692491427161681700403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2815179977139097817867741 1055692491427161681700403)
                ·
                  refine ⟨1583538737140742522550605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055692491427161681700403 1583538737140742522550605)
                  ·
                    refine ⟨593827026427778445956477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583538737140742522550605 593827026427778445956477)
                    ·
                      rfl

theorem cell22_1734711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_1734711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734711 prefixEnd_1734711 := by exact prefixLift 1734711
  have htrace : WordTrace (prefixWord ++ tailWord_1734711) baseStart_1734711 baseEnd_1734711 := by
    simpa [prefixWord, tailWord_1734711, baseEnd_1734711] using wordTrace_append hprefix tailTrace_1734711
  have hstable : (prefixWord ++ tailWord_1734711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734711).length < 2 ^ (prefixWord ++ tailWord_1734711).sum := by decide
  have hdescent : baseEnd_1734711 < baseStart_1734711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734737 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1734737 : Nat := 118140960795 + 1734737 * 2 ^ 59
def prefixEnd_1734737 : Nat := 4983230072969 + 3 ^ 40 * 1734737 * 2
def baseEnd_1734737 : Nat := 593835926759123044806397

theorem tailTrace_1734737 : CollatzResearch.WordTrace tailWord_1734737 prefixEnd_1734737 593835926759123044806397 := by
  unfold tailWord_1734737
  simp only [CollatzResearch.WordTrace]
  refine ⟨63271056316351593337490465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42180704210901062224993643 63271056316351593337490465)
  ·
    refine ⟨47453292237263695003117849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63271056316351593337490465 47453292237263695003117849)
    ·
      refine ⟨35589969177947771252338387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47453292237263695003117849 35589969177947771252338387)
      ·
        refine ⟨53384953766921656878507581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35589969177947771252338387 53384953766921656878507581)
        ·
          refine ⟨20019357662595621329440343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53384953766921656878507581 20019357662595621329440343)
          ·
            refine ⟨30029036493893431994160515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20019357662595621329440343 30029036493893431994160515)
            ·
              refine ⟨45043554740840147991240773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30029036493893431994160515 45043554740840147991240773)
              ·
                refine ⟨8445666513907527748357645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45043554740840147991240773 8445666513907527748357645)
                ·
                  refine ⟨3167124942715322905634117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8445666513907527748357645 3167124942715322905634117)
                  ·
                    refine ⟨593835926759123044806397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167124942715322905634117 593835926759123044806397)
                    ·
                      rfl

theorem cell22_1734737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1734737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734737 prefixEnd_1734737 := by exact prefixLift 1734737
  have htrace : WordTrace (prefixWord ++ tailWord_1734737) baseStart_1734737 baseEnd_1734737 := by
    simpa [prefixWord, tailWord_1734737, baseEnd_1734737] using wordTrace_append hprefix tailTrace_1734737
  have hstable : (prefixWord ++ tailWord_1734737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734737).length < 2 ^ (prefixWord ++ tailWord_1734737).sum := by decide
  have hdescent : baseEnd_1734737 < baseStart_1734737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734741 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 5]
def baseStart_1734741 : Nat := 118140960795 + 1734741 * 2 ^ 59
def prefixEnd_1734741 : Nat := 4983230072969 + 3 ^ 40 * 1734741 * 2
def baseEnd_1734741 : Nat := 197945765346956122568795

theorem tailTrace_1734741 : CollatzResearch.WordTrace tailWord_1734741 prefixEnd_1734741 197945765346956122568795 := by
  unfold tailWord_1734741
  simp only [CollatzResearch.WordTrace]
  refine ⟨63271202208337102020636077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42180801472224734680424051 63271202208337102020636077)
  ·
    refine ⟨23726700828126413257738529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63271202208337102020636077 23726700828126413257738529)
    ·
      refine ⟨17795025621094809943303897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23726700828126413257738529 17795025621094809943303897)
      ·
        refine ⟨13346269215821107457477923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17795025621094809943303897 13346269215821107457477923)
        ·
          refine ⟨20019403823731661186216885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13346269215821107457477923 20019403823731661186216885)
          ·
            refine ⟨1876819108474843236207833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20019403823731661186216885 1876819108474843236207833)
            ·
              refine ⟨1407614331356132427155875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1876819108474843236207833 1407614331356132427155875)
              ·
                refine ⟨2111421497034198640733813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407614331356132427155875 2111421497034198640733813)
                ·
                  refine ⟨197945765346956122568795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2111421497034198640733813 197945765346956122568795)
                  ·
                    rfl

theorem cell22_1734741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_1734741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734741 prefixEnd_1734741 := by exact prefixLift 1734741
  have htrace : WordTrace (prefixWord ++ tailWord_1734741) baseStart_1734741 baseEnd_1734741 := by
    simpa [prefixWord, tailWord_1734741, baseEnd_1734741] using wordTrace_append hprefix tailTrace_1734741
  have hstable : (prefixWord ++ tailWord_1734741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734741).length < 2 ^ (prefixWord ++ tailWord_1734741).sum := by decide
  have hdescent : baseEnd_1734741 < baseStart_1734741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734767 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 3, 5]
def baseStart_1734767 : Nat := 118140960795 + 1734767 * 2 ^ 59
def prefixEnd_1734767 : Nat := 4983230072969 + 3 ^ 40 * 1734767 * 2
def baseEnd_1734767 : Nat := 593846196372212966556305

theorem tailTrace_1734767 : CollatzResearch.WordTrace tailWord_1734767 prefixEnd_1734767 593846196372212966556305 := by
  unfold tailWord_1734767
  simp only [CollatzResearch.WordTrace]
  refine ⟨63272150506242908461082555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42181433670828605640721703 63272150506242908461082555)
  ·
    refine ⟨94908225759364362691623833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63272150506242908461082555 94908225759364362691623833)
    ·
      refine ⟨71181169319523272018717875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94908225759364362691623833 71181169319523272018717875)
      ·
        refine ⟨106771753979284908028076813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71181169319523272018717875 106771753979284908028076813)
        ·
          refine ⟨40039407742231840510528805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106771753979284908028076813 40039407742231840510528805)
          ·
            refine ⟨7507388951668470095724151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40039407742231840510528805 7507388951668470095724151)
            ·
              refine ⟨11261083427502705143586227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507388951668470095724151 11261083427502705143586227)
              ·
                refine ⟨16891625141254057715379341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261083427502705143586227 16891625141254057715379341)
                ·
                  refine ⟨6334359427970271643267253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16891625141254057715379341 6334359427970271643267253)
                  ·
                    refine ⟨593846196372212966556305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6334359427970271643267253 593846196372212966556305)
                    ·
                      rfl

theorem cell22_1734767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_1734767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734767 prefixEnd_1734767 := by exact prefixLift 1734767
  have htrace : WordTrace (prefixWord ++ tailWord_1734767) baseStart_1734767 baseEnd_1734767 := by
    simpa [prefixWord, tailWord_1734767, baseEnd_1734767] using wordTrace_append hprefix tailTrace_1734767
  have hstable : (prefixWord ++ tailWord_1734767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734767).length < 2 ^ (prefixWord ++ tailWord_1734767).sum := by decide
  have hdescent : baseEnd_1734767 < baseStart_1734767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734769 : List Nat := [1, 2, 2, 2, 1, 1, 4, 5, 4]
def baseStart_1734769 : Nat := 118140960795 + 1734769 * 2 ^ 59
def prefixEnd_1734769 : Nat := 4983230072969 + 3 ^ 40 * 1734769 * 2
def baseEnd_1734769 : Nat := 197948960337695209335433

theorem tailTrace_1734769 : CollatzResearch.WordTrace tailWord_1734769 prefixEnd_1734769 197948960337695209335433 := by
  unfold tailWord_1734769
  simp only [CollatzResearch.WordTrace]
  refine ⟨63272223452235662802655361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42181482301490441868436907 63272223452235662802655361)
  ·
    refine ⟨47454167589176747101991521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63272223452235662802655361 47454167589176747101991521)
    ·
      refine ⟨35590625691882560326493641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47454167589176747101991521 35590625691882560326493641)
      ·
        refine ⟨26692969268911920244870231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35590625691882560326493641 26692969268911920244870231)
        ·
          refine ⟨40039453903367880367305347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26692969268911920244870231 40039453903367880367305347)
          ·
            refine ⟨60059180855051820550958021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40039453903367880367305347 60059180855051820550958021)
            ·
              refine ⟨11261096410322216353304629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60059180855051820550958021 11261096410322216353304629)
              ·
                refine ⟨1055727788467707783122309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11261096410322216353304629 1055727788467707783122309)
                ·
                  refine ⟨197948960337695209335433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055727788467707783122309 197948960337695209335433)
                  ·
                    rfl

theorem cell22_1734769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_1734769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734769 prefixEnd_1734769 := by exact prefixLift 1734769
  have htrace : WordTrace (prefixWord ++ tailWord_1734769) baseStart_1734769 baseEnd_1734769 := by
    simpa [prefixWord, tailWord_1734769, baseEnd_1734769] using wordTrace_append hprefix tailTrace_1734769
  have hstable : (prefixWord ++ tailWord_1734769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734769).length < 2 ^ (prefixWord ++ tailWord_1734769).sum := by decide
  have hdescent : baseEnd_1734769 < baseStart_1734769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734816 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 2, 4]
def baseStart_1734816 : Nat := 118140960795 + 1734816 * 2 ^ 59
def prefixEnd_1734816 : Nat := 4983230072969 + 3 ^ 40 * 1734816 * 2
def baseEnd_1734816 : Nat := 593862970073593172081155

theorem tailTrace_1734816 : CollatzResearch.WordTrace tailWord_1734816 prefixEnd_1734816 593862970073593172081155 := by
  unfold tailWord_1734816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31636968841532694914808151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42182625122043593219744201 31636968841532694914808151)
  ·
    refine ⟨47455453262299042372212227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31636968841532694914808151 47455453262299042372212227)
    ·
      refine ⟨71183179893448563558318341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47455453262299042372212227 71183179893448563558318341)
      ·
        refine ⟨13346846230021605667184689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71183179893448563558318341 13346846230021605667184689)
        ·
          refine ⟨10010134672516204250388517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13346846230021605667184689 10010134672516204250388517)
          ·
            refine ⟨1876900251096788296947847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10010134672516204250388517 1876900251096788296947847)
            ·
              refine ⟨2815350376645182445421771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876900251096788296947847 2815350376645182445421771)
              ·
                refine ⟨4223025564967773668132657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815350376645182445421771 4223025564967773668132657)
                ·
                  refine ⟨3167269173725830251099493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4223025564967773668132657 3167269173725830251099493)
                  ·
                    refine ⟨593862970073593172081155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167269173725830251099493 593862970073593172081155)
                    ·
                      rfl

theorem cell22_1734816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_1734816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734816 prefixEnd_1734816 := by exact prefixLift 1734816
  have htrace : WordTrace (prefixWord ++ tailWord_1734816) baseStart_1734816 baseEnd_1734816 := by
    simpa [prefixWord, tailWord_1734816, baseEnd_1734816] using wordTrace_append hprefix tailTrace_1734816
  have hstable : (prefixWord ++ tailWord_1734816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734816).length < 2 ^ (prefixWord ++ tailWord_1734816).sum := by decide
  have hdescent : baseEnd_1734816 < baseStart_1734816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734857 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_1734857 : Nat := 118140960795 + 1734857 * 2 ^ 59
def prefixEnd_1734857 : Nat := 4983230072969 + 3 ^ 40 * 1734857 * 2
def baseEnd_1734857 : Nat := 593877005211482731806029

theorem tailTrace_1734857 : CollatzResearch.WordTrace tailWord_1734857 prefixEnd_1734857 593877005211482731806029 := by
  unfold tailWord_1734857
  simp only [CollatzResearch.WordTrace]
  refine ⟨63275433075916853831858825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42183622050611235887905883 63275433075916853831858825)
  ·
    refine ⟨47456574806937640373894119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63275433075916853831858825 47456574806937640373894119)
    ·
      refine ⟨71184862210406460560841179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47456574806937640373894119 71184862210406460560841179)
      ·
        refine ⟨106777293315609690841261769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71184862210406460560841179 106777293315609690841261769)
        ·
          refine ⟨80082969986707268130946327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106777293315609690841261769 80082969986707268130946327)
          ·
            refine ⟨120124454980060902196419491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80082969986707268130946327 120124454980060902196419491)
            ·
              refine ⟨180186682470091353294629237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120124454980060902196419491 180186682470091353294629237)
              ·
                refine ⟨16892501481571064371371491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180186682470091353294629237 16892501481571064371371491)
                ·
                  refine ⟨25338752222356596557057237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16892501481571064371371491 25338752222356596557057237)
                  ·
                    refine ⟨593877005211482731806029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25338752222356596557057237 593877005211482731806029)
                    ·
                      rfl

theorem cell22_1734857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_1734857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734857 prefixEnd_1734857 := by exact prefixLift 1734857
  have htrace : WordTrace (prefixWord ++ tailWord_1734857) baseStart_1734857 baseEnd_1734857 := by
    simpa [prefixWord, tailWord_1734857, baseEnd_1734857] using wordTrace_append hprefix tailTrace_1734857
  have hstable : (prefixWord ++ tailWord_1734857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734857).length < 2 ^ (prefixWord ++ tailWord_1734857).sum := by decide
  have hdescent : baseEnd_1734857 < baseStart_1734857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734949 : List Nat := [1, 3, 1, 2, 5, 10]
def baseStart_1734949 : Nat := 118140960795 + 1734949 * 2 ^ 59
def prefixEnd_1734949 : Nat := 4983230072969 + 3 ^ 40 * 1734949 * 2
def baseEnd_1734949 : Nat := 7332203687550927882787

theorem tailTrace_1734949 : CollatzResearch.WordTrace tailWord_1734949 prefixEnd_1734949 7332203687550927882787 := by
  unfold tailWord_1734949
  simp only [CollatzResearch.WordTrace]
  refine ⟨63278788591583553544207901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42185859061055702362805267 63278788591583553544207901)
  ·
    refine ⟨23729545721843832579077963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63278788591583553544207901 23729545721843832579077963)
    ·
      refine ⟨35594318582765748868616945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23729545721843832579077963 35594318582765748868616945)
      ·
        refine ⟨26695738937074311651462709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35594318582765748868616945 26695738937074311651462709)
        ·
          refine ⟨2502725525350716717324629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26695738937074311651462709 2502725525350716717324629)
          ·
            refine ⟨7332203687550927882787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2502725525350716717324629 7332203687550927882787)
            ·
              rfl

theorem cell22_1734949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 10].length) (baseStart_1734949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1734949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1734949 prefixEnd_1734949 := by exact prefixLift 1734949
  have htrace : WordTrace (prefixWord ++ tailWord_1734949) baseStart_1734949 baseEnd_1734949 := by
    simpa [prefixWord, tailWord_1734949, baseEnd_1734949] using wordTrace_append hprefix tailTrace_1734949
  have hstable : (prefixWord ++ tailWord_1734949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734949).length < 2 ^ (prefixWord ++ tailWord_1734949).sum := by decide
  have hdescent : baseEnd_1734949 < baseStart_1734949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735004 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1735004 : Nat := 118140960795 + 1735004 * 2 ^ 59
def prefixEnd_1735004 : Nat := 4983230072969 + 3 ^ 40 * 1735004 * 2
def baseEnd_1735004 : Nat := 593927326315623348380579

theorem tailTrace_1735004 : CollatzResearch.WordTrace tailWord_1735004 prefixEnd_1735004 593927326315623348380579 := by
  unfold tailWord_1735004
  simp only [CollatzResearch.WordTrace]
  refine ⟨31640397303192148968730033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42187196404256198624973377 31640397303192148968730033)
  ·
    refine ⟨23730297977394111726547525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31640397303192148968730033 23730297977394111726547525)
    ·
      refine ⟨4449430870761395948727661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23730297977394111726547525 4449430870761395948727661)
      ·
        refine ⟨1668536576535523480772873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4449430870761395948727661 1668536576535523480772873)
        ·
          refine ⟨1251402432401642610579655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668536576535523480772873 1251402432401642610579655)
          ·
            refine ⟨1877103648602463915869483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251402432401642610579655 1877103648602463915869483)
            ·
              refine ⟨2815655472903695873804225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877103648602463915869483 2815655472903695873804225)
              ·
                refine ⟨2111741604677771905353169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815655472903695873804225 2111741604677771905353169)
                ·
                  refine ⟨1583806203508328929014877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2111741604677771905353169 1583806203508328929014877)
                  ·
                    refine ⟨593927326315623348380579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583806203508328929014877 593927326315623348380579)
                    ·
                      rfl

theorem cell22_1735004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1735004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735004 prefixEnd_1735004 := by exact prefixLift 1735004
  have htrace : WordTrace (prefixWord ++ tailWord_1735004) baseStart_1735004 baseEnd_1735004 := by
    simpa [prefixWord, tailWord_1735004, baseEnd_1735004] using wordTrace_append hprefix tailTrace_1735004
  have hstable : (prefixWord ++ tailWord_1735004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735004).length < 2 ^ (prefixWord ++ tailWord_1735004).sum := by decide
  have hdescent : baseEnd_1735004 < baseStart_1735004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735015 : List Nat := [1, 1, 5, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1735015 : Nat := 118140960795 + 1735015 * 2 ^ 59
def prefixEnd_1735015 : Nat := 4983230072969 + 3 ^ 40 * 1735015 * 2
def baseEnd_1735015 : Nat := 593931091840422986355545

theorem tailTrace_1735015 : CollatzResearch.WordTrace tailWord_1735015 prefixEnd_1735015 593931091840422986355545 := by
  unfold tailWord_1735015
  simp only [CollatzResearch.WordTrace]
  refine ⟨63281195809344446816110499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42187463872896297877406999 63281195809344446816110499)
  ·
    refine ⟨94921793714016670224165749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63281195809344446816110499 94921793714016670224165749)
    ·
      refine ⟨8898918160689062833515539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94921793714016670224165749 8898918160689062833515539)
      ·
        refine ⟨13348377241033594250273309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898918160689062833515539 13348377241033594250273309)
        ·
          refine ⟨5005641465387597843852491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13348377241033594250273309 5005641465387597843852491)
          ·
            refine ⟨7508462198081396765778737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005641465387597843852491 7508462198081396765778737)
            ·
              refine ⟨5631346648561047574334053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7508462198081396765778737 5631346648561047574334053)
              ·
                refine ⟨1055877496605196420187635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5631346648561047574334053 1055877496605196420187635)
                ·
                  refine ⟨1583816244907794630281453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055877496605196420187635 1583816244907794630281453)
                  ·
                    refine ⟨593931091840422986355545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583816244907794630281453 593931091840422986355545)
                    ·
                      rfl

theorem cell22_1735015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1735015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735015 prefixEnd_1735015 := by exact prefixLift 1735015
  have htrace : WordTrace (prefixWord ++ tailWord_1735015) baseStart_1735015 baseEnd_1735015 := by
    simpa [prefixWord, tailWord_1735015, baseEnd_1735015] using wordTrace_append hprefix tailTrace_1735015
  have hstable : (prefixWord ++ tailWord_1735015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735015).length < 2 ^ (prefixWord ++ tailWord_1735015).sum := by decide
  have hdescent : baseEnd_1735015 < baseStart_1735015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735026 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1735026 : Nat := 118140960795 + 1735026 * 2 ^ 59
def prefixEnd_1735026 : Nat := 4983230072969 + 3 ^ 40 * 1735026 * 2
def baseEnd_1735026 : Nat := 593934857365222624330511

theorem tailTrace_1735026 : CollatzResearch.WordTrace tailWord_1735026 prefixEnd_1735026 593934857365222624330511 := by
  unfold tailWord_1735026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15820399253076148923690233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42187731341536397129840621 15820399253076148923690233)
  ·
    refine ⟨11865299439807111692767675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15820399253076148923690233 11865299439807111692767675)
    ·
      refine ⟨17797949159710667539151513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11865299439807111692767675 17797949159710667539151513)
      ·
        refine ⟨13348461869783000654363635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17797949159710667539151513 13348461869783000654363635)
        ·
          refine ⟨20022692804674500981545453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13348461869783000654363635 20022692804674500981545453)
          ·
            refine ⟨7508509801752937868079545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20022692804674500981545453 7508509801752937868079545)
            ·
              refine ⟨5631382351314703401059659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7508509801752937868079545 5631382351314703401059659)
              ·
                refine ⟨8447073526972055101589489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631382351314703401059659 8447073526972055101589489)
                ·
                  refine ⟨6335305145229041326192117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8447073526972055101589489 6335305145229041326192117)
                  ·
                    refine ⟨593934857365222624330511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6335305145229041326192117 593934857365222624330511)
                    ·
                      rfl

theorem cell22_1735026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1735026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735026 prefixEnd_1735026 := by exact prefixLift 1735026
  have htrace : WordTrace (prefixWord ++ tailWord_1735026) baseStart_1735026 baseEnd_1735026 := by
    simpa [prefixWord, tailWord_1735026, baseEnd_1735026] using wordTrace_append hprefix tailTrace_1735026
  have hstable : (prefixWord ++ tailWord_1735026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735026).length < 2 ^ (prefixWord ++ tailWord_1735026).sum := by decide
  have hdescent : baseEnd_1735026 < baseStart_1735026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735092 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1735092 : Nat := 118140960795 + 1735092 * 2 ^ 59
def prefixEnd_1735092 : Nat := 4983230072969 + 3 ^ 40 * 1735092 * 2
def baseEnd_1735092 : Nat := 593957450514020452180309

theorem tailTrace_1735092 : CollatzResearch.WordTrace tailWord_1735092 prefixEnd_1735092 593957450514020452180309 := by
  unfold tailWord_1735092
  simp only [CollatzResearch.WordTrace]
  refine ⟨31642002115032744483331765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42189336153376992644442353 31642002115032744483331765)
  ·
    refine ⟨2966437698284319795312353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31642002115032744483331765 2966437698284319795312353)
    ·
      refine ⟨2224828273713239846484265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2966437698284319795312353 2224828273713239846484265)
      ·
        refine ⟨1668621205284929884863199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224828273713239846484265 1668621205284929884863199)
        ·
          refine ⟨2502931807927394827294799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668621205284929884863199 2502931807927394827294799)
          ·
            refine ⟨3754397711891092240942199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502931807927394827294799 3754397711891092240942199)
            ·
              refine ⟨5631596567836638361413299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754397711891092240942199 5631596567836638361413299)
              ·
                refine ⟨8447394851754957542119949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631596567836638361413299 8447394851754957542119949)
                ·
                  refine ⟨3167773069408109078294981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8447394851754957542119949 3167773069408109078294981)
                  ·
                    refine ⟨593957450514020452180309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167773069408109078294981 593957450514020452180309)
                    ·
                      rfl

theorem cell22_1735092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1735092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735092 prefixEnd_1735092 := by exact prefixLift 1735092
  have htrace : WordTrace (prefixWord ++ tailWord_1735092) baseStart_1735092 baseEnd_1735092 := by
    simpa [prefixWord, tailWord_1735092, baseEnd_1735092] using wordTrace_append hprefix tailTrace_1735092
  have hstable : (prefixWord ++ tailWord_1735092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735092).length < 2 ^ (prefixWord ++ tailWord_1735092).sum := by decide
  have hdescent : baseEnd_1735092 < baseStart_1735092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735101 : List Nat := [1, 4, 1, 2, 2, 2, 2, 8]
def baseStart_1735101 : Nat := 118140960795 + 1735101 * 2 ^ 59
def prefixEnd_1735101 : Nat := 4983230072969 + 3 ^ 40 * 1735101 * 2
def baseEnd_1735101 : Nat := 65995614599771936522809

theorem tailTrace_1735101 : CollatzResearch.WordTrace tailWord_1735101 prefixEnd_1735101 65995614599771936522809 := by
  unfold tailWord_1735101
  simp only [CollatzResearch.WordTrace]
  refine ⟨63284332487032883503741157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42189554991355255669160771 63284332487032883503741157)
  ·
    refine ⟨11865812341318665656951467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63284332487032883503741157 11865812341318665656951467)
    ·
      refine ⟨17798718511977998485427201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11865812341318665656951467 17798718511977998485427201)
      ·
        refine ⟨13349038883983498864070401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17798718511977998485427201 13349038883983498864070401)
        ·
          refine ⟨10011779162987624148052801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13349038883983498864070401 10011779162987624148052801)
          ·
            refine ⟨7508834372240718111039601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10011779162987624148052801 7508834372240718111039601)
            ·
              refine ⟨5631625779180538583279701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7508834372240718111039601 5631625779180538583279701)
              ·
                refine ⟨65995614599771936522809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5631625779180538583279701 65995614599771936522809)
                ·
                  rfl

theorem cell22_1735101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 8].length) (baseStart_1735101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735101 prefixEnd_1735101 := by exact prefixLift 1735101
  have htrace : WordTrace (prefixWord ++ tailWord_1735101) baseStart_1735101 baseEnd_1735101 := by
    simpa [prefixWord, tailWord_1735101, baseEnd_1735101] using wordTrace_append hprefix tailTrace_1735101
  have hstable : (prefixWord ++ tailWord_1735101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735101).length < 2 ^ (prefixWord ++ tailWord_1735101).sum := by decide
  have hdescent : baseEnd_1735101 < baseStart_1735101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735150 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1735150 : Nat := 118140960795 + 1735150 * 2 ^ 59
def prefixEnd_1735150 : Nat := 4983230072969 + 3 ^ 40 * 1735150 * 2
def baseEnd_1735150 : Nat := 593977305099327634230131

theorem tailTrace_1735150 : CollatzResearch.WordTrace tailWord_1735150 prefixEnd_1735150 593977305099327634230131 := by
  unfold tailWord_1735150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910764957981920609034363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42190746442570243248183269 7910764957981920609034363)
  ·
    refine ⟨11866147436972880913551545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7910764957981920609034363 11866147436972880913551545)
    ·
      refine ⟨8899610577729660685163659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11866147436972880913551545 8899610577729660685163659)
      ·
        refine ⟨13349415866594491027745489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8899610577729660685163659 13349415866594491027745489)
        ·
          refine ⟨10012061899945868270809117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13349415866594491027745489 10012061899945868270809117)
          ·
            refine ⟨3754523212479700601553419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10012061899945868270809117 3754523212479700601553419)
            ·
              refine ⟨5631784818719550902330129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754523212479700601553419 5631784818719550902330129)
              ·
                refine ⟨4223838614039663176747597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5631784818719550902330129 4223838614039663176747597)
                ·
                  refine ⟨1583939480264873691280349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4223838614039663176747597 1583939480264873691280349)
                  ·
                    refine ⟨593977305099327634230131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583939480264873691280349 593977305099327634230131)
                    ·
                      rfl

theorem cell22_1735150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1735150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735150 prefixEnd_1735150 := by exact prefixLift 1735150
  have htrace : WordTrace (prefixWord ++ tailWord_1735150) baseStart_1735150 baseEnd_1735150 := by
    simpa [prefixWord, tailWord_1735150, baseEnd_1735150] using wordTrace_append hprefix tailTrace_1735150
  have hstable : (prefixWord ++ tailWord_1735150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735150).length < 2 ^ (prefixWord ++ tailWord_1735150).sum := by decide
  have hdescent : baseEnd_1735150 < baseStart_1735150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735180 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 5]
def baseStart_1735180 : Nat := 118140960795 + 1735180 * 2 ^ 59
def prefixEnd_1735180 : Nat := 4983230072969 + 3 ^ 40 * 1735180 * 2
def baseEnd_1735180 : Nat := 197995858237472518660013

theorem tailTrace_1735180 : CollatzResearch.WordTrace tailWord_1735180 prefixEnd_1735180 197995858237472518660013 := by
  unfold tailWord_1735180
  simp only [CollatzResearch.WordTrace]
  refine ⟨31643606926873339997933497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42191475902497786663911329 31643606926873339997933497)
  ·
    refine ⟨23732705195155004998450123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31643606926873339997933497 23732705195155004998450123)
    ·
      refine ⟨35599057792732507497675185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23732705195155004998450123 35599057792732507497675185)
      ·
        refine ⟨26699293344549380623256389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35599057792732507497675185 26699293344549380623256389)
        ·
          refine ⟨5006117502103008866860573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26699293344549380623256389 5006117502103008866860573)
          ·
            refine ⟨1877294063288628325072715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5006117502103008866860573 1877294063288628325072715)
            ·
              refine ⟨2815941094932942487609073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877294063288628325072715 2815941094932942487609073)
              ·
                refine ⟨2111955821199706865706805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815941094932942487609073 2111955821199706865706805)
                ·
                  refine ⟨197995858237472518660013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2111955821199706865706805 197995858237472518660013)
                  ·
                    rfl

theorem cell22_1735180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_1735180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735180 prefixEnd_1735180 := by exact prefixLift 1735180
  have htrace : WordTrace (prefixWord ++ tailWord_1735180) baseStart_1735180 baseEnd_1735180 := by
    simpa [prefixWord, tailWord_1735180, baseEnd_1735180] using wordTrace_append hprefix tailTrace_1735180
  have hstable : (prefixWord ++ tailWord_1735180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735180).length < 2 ^ (prefixWord ++ tailWord_1735180).sum := by decide
  have hdescent : baseEnd_1735180 < baseStart_1735180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735210 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1735210 : Nat := 118140960795 + 1735210 * 2 ^ 59
def prefixEnd_1735210 : Nat := 4983230072969 + 3 ^ 40 * 1735210 * 2
def baseEnd_1735210 : Nat := 593997844325507477729947

theorem tailTrace_1735210 : CollatzResearch.WordTrace tailWord_1735210 prefixEnd_1735210 593997844325507477729947 := by
  unfold tailWord_1735210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15822077010909498779864771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42192205362425330079639389 15822077010909498779864771)
  ·
    refine ⟨23733115516364248169797157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15822077010909498779864771 23733115516364248169797157)
    ·
      refine ⟨4449959159318296531836967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23733115516364248169797157 4449959159318296531836967)
      ·
        refine ⟨6674938738977444797755451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449959159318296531836967 6674938738977444797755451)
        ·
          refine ⟨10012408108466167196633177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674938738977444797755451 10012408108466167196633177)
          ·
            refine ⟨7509306081349625397474883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10012408108466167196633177 7509306081349625397474883)
            ·
              refine ⟨11263959122024438096212325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7509306081349625397474883 11263959122024438096212325)
              ·
                refine ⟨2111992335379582143039811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11263959122024438096212325 2111992335379582143039811)
                ·
                  refine ⟨3167988503069373214559717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111992335379582143039811 3167988503069373214559717)
                  ·
                    refine ⟨593997844325507477729947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167988503069373214559717 593997844325507477729947)
                    ·
                      rfl

theorem cell22_1735210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1735210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735210 prefixEnd_1735210 := by exact prefixLift 1735210
  have htrace : WordTrace (prefixWord ++ tailWord_1735210) baseStart_1735210 baseEnd_1735210 := by
    simpa [prefixWord, tailWord_1735210, baseEnd_1735210] using wordTrace_append hprefix tailTrace_1735210
  have hstable : (prefixWord ++ tailWord_1735210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735210).length < 2 ^ (prefixWord ++ tailWord_1735210).sum := by decide
  have hdescent : baseEnd_1735210 < baseStart_1735210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735223 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 6, 3]
def baseStart_1735223 : Nat := 118140960795 + 1735223 * 2 ^ 59
def prefixEnd_1735223 : Nat := 4983230072969 + 3 ^ 40 * 1735223 * 2
def baseEnd_1735223 : Nat := 594002294491179777154907

theorem tailTrace_1735223 : CollatzResearch.WordTrace tailWord_1735223 prefixEnd_1735223 594002294491179777154907 := by
  unfold tailWord_1735223
  simp only [CollatzResearch.WordTrace]
  refine ⟨63288782192590898339682323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42192521461727265559788215 63288782192590898339682323)
  ·
    refine ⟨94933173288886347509523485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63288782192590898339682323 94933173288886347509523485)
    ·
      refine ⟨35599939983332380316071307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94933173288886347509523485 35599939983332380316071307)
      ·
        refine ⟨53399909974998570474106961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35599939983332380316071307 53399909974998570474106961)
        ·
          refine ⟨40049932481248927855580221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53399909974998570474106961 40049932481248927855580221)
          ·
            refine ⟨15018724680468347945842583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40049932481248927855580221 15018724680468347945842583)
            ·
              refine ⟨22528087020702521918763875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15018724680468347945842583 22528087020702521918763875)
              ·
                refine ⟨33792130531053782878145813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22528087020702521918763875 33792130531053782878145813)
                ·
                  refine ⟨1584006118643146072413085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33792130531053782878145813 1584006118643146072413085)
                  ·
                    refine ⟨594002294491179777154907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1584006118643146072413085 594002294491179777154907)
                    ·
                      rfl

theorem cell22_1735223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_1735223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735223 prefixEnd_1735223 := by exact prefixLift 1735223
  have htrace : WordTrace (prefixWord ++ tailWord_1735223) baseStart_1735223 baseEnd_1735223 := by
    simpa [prefixWord, tailWord_1735223, baseEnd_1735223] using wordTrace_append hprefix tailTrace_1735223
  have hstable : (prefixWord ++ tailWord_1735223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735223).length < 2 ^ (prefixWord ++ tailWord_1735223).sum := by decide
  have hdescent : baseEnd_1735223 < baseStart_1735223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735242 : List Nat := [3, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_1735242 : Nat := 118140960795 + 1735242 * 2 ^ 59
def prefixEnd_1735242 : Nat := 4983230072969 + 3 ^ 40 * 1735242 * 2
def baseEnd_1735242 : Nat := 198002932859823353643283

theorem tailTrace_1735242 : CollatzResearch.WordTrace tailWord_1735242 prefixEnd_1735242 198002932859823353643283 := by
  unfold tailWord_1735242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15822368794880516146155995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42192983453014709723082653 15822368794880516146155995)
  ·
    refine ⟨23733553192320774219233993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15822368794880516146155995 23733553192320774219233993)
    ·
      refine ⟨17800164894240580664425495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23733553192320774219233993 17800164894240580664425495)
      ·
        refine ⟨26700247341360870996638243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17800164894240580664425495 26700247341360870996638243)
        ·
          refine ⟨40050371012041306494957365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26700247341360870996638243 40050371012041306494957365)
          ·
            refine ⟨3754722282378872483902253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40050371012041306494957365 3754722282378872483902253)
            ·
              refine ⟨1408020855892077181463345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3754722282378872483902253 1408020855892077181463345)
              ·
                refine ⟨1056015641919057886097509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408020855892077181463345 1056015641919057886097509)
                ·
                  refine ⟨198002932859823353643283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056015641919057886097509 198002932859823353643283)
                  ·
                    rfl

theorem cell22_1735242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_1735242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735242 prefixEnd_1735242 := by exact prefixLift 1735242
  have htrace : WordTrace (prefixWord ++ tailWord_1735242) baseStart_1735242 baseEnd_1735242 := by
    simpa [prefixWord, tailWord_1735242, baseEnd_1735242] using wordTrace_append hprefix tailTrace_1735242
  have hstable : (prefixWord ++ tailWord_1735242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735242).length < 2 ^ (prefixWord ++ tailWord_1735242).sum := by decide
  have hdescent : baseEnd_1735242 < baseStart_1735242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735272 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_1735272 : Nat := 118140960795 + 1735272 * 2 ^ 59
def prefixEnd_1735272 : Nat := 4983230072969 + 3 ^ 40 * 1735272 * 2
def baseEnd_1735272 : Nat := 594019068192559982679757

theorem tailTrace_1735272 : CollatzResearch.WordTrace tailWord_1735272 prefixEnd_1735272 594019068192559982679757 := by
  unfold tailWord_1735272
  simp only [CollatzResearch.WordTrace]
  refine ⟨31645284684706689854108035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42193712912942253138810713 31645284684706689854108035)
  ·
    refine ⟨47467927027060034781162053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31645284684706689854108035 47467927027060034781162053)
    ·
      refine ⟨8900236317573756521467885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47467927027060034781162053 8900236317573756521467885)
      ·
        refine ⟨3337588619090158695550457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8900236317573756521467885 3337588619090158695550457)
        ·
          refine ⟨2503191464317619021662843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3337588619090158695550457 2503191464317619021662843)
          ·
            refine ⟨3754787196476428532494265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503191464317619021662843 3754787196476428532494265)
            ·
              refine ⟨2816090397357321399370699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754787196476428532494265 2816090397357321399370699)
              ·
                refine ⟨4224135596035982099056049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816090397357321399370699 4224135596035982099056049)
                ·
                  refine ⟨3168101697026986574292037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224135596035982099056049 3168101697026986574292037)
                  ·
                    refine ⟨594019068192559982679757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3168101697026986574292037 594019068192559982679757)
                    ·
                      rfl

theorem cell22_1735272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_1735272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735272 prefixEnd_1735272 := by exact prefixLift 1735272
  have htrace : WordTrace (prefixWord ++ tailWord_1735272) baseStart_1735272 baseEnd_1735272 := by
    simpa [prefixWord, tailWord_1735272, baseEnd_1735272] using wordTrace_append hprefix tailTrace_1735272
  have hstable : (prefixWord ++ tailWord_1735272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735272).length < 2 ^ (prefixWord ++ tailWord_1735272).sum := by decide
  have hdescent : baseEnd_1735272 < baseStart_1735272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735360 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 6]
def baseStart_1735360 : Nat := 118140960795 + 1735360 * 2 ^ 59
def prefixEnd_1735360 : Nat := 4983230072969 + 3 ^ 40 * 1735360 * 2
def baseEnd_1735360 : Nat := 198016397463652362159829

theorem tailTrace_1735360 : CollatzResearch.WordTrace tailWord_1735360 prefixEnd_1735360 198016397463652362159829 := by
  unfold tailWord_1735360
  simp only [CollatzResearch.WordTrace]
  refine ⟨31646889496547285368709767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42195852662063047158279689 31646889496547285368709767)
  ·
    refine ⟨47470334244820928053064651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31646889496547285368709767 47470334244820928053064651)
    ·
      refine ⟨71205501367231392079596977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47470334244820928053064651 71205501367231392079596977)
      ·
        refine ⟨53404126025423544059697733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71205501367231392079596977 53404126025423544059697733)
        ·
          refine ⟨10013273629766914511193325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53404126025423544059697733 10013273629766914511193325)
          ·
            refine ⟨3754977611162592941697497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10013273629766914511193325 3754977611162592941697497)
            ·
              refine ⟨2816233208371944706273123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754977611162592941697497 2816233208371944706273123)
              ·
                refine ⟨4224349812557917059409685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816233208371944706273123 4224349812557917059409685)
                ·
                  refine ⟨198016397463652362159829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4224349812557917059409685 198016397463652362159829)
                  ·
                    rfl

theorem cell22_1735360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_1735360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735360 prefixEnd_1735360 := by exact prefixLift 1735360
  have htrace : WordTrace (prefixWord ++ tailWord_1735360) baseStart_1735360 baseEnd_1735360 := by
    simpa [prefixWord, tailWord_1735360, baseEnd_1735360] using wordTrace_append hprefix tailTrace_1735360
  have hstable : (prefixWord ++ tailWord_1735360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735360).length < 2 ^ (prefixWord ++ tailWord_1735360).sum := by decide
  have hdescent : baseEnd_1735360 < baseStart_1735360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735422 : List Nat := [4, 2, 2, 1, 2, 2, 2, 7]
def baseStart_1735422 : Nat := 118140960795 + 1735422 * 2 ^ 59
def prefixEnd_1735422 : Nat := 4983230072969 + 3 ^ 40 * 1735422 * 2
def baseEnd_1735422 : Nat := 66007824028667732381033

theorem tailTrace_1735422 : CollatzResearch.WordTrace tailWord_1735422 prefixEnd_1735422 66007824028667732381033 := by
  unfold tailWord_1735422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912005039858744415772065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42197360212579970217451013 7912005039858744415772065)
  ·
    refine ⟨5934003779894058311829049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7912005039858744415772065 5934003779894058311829049)
    ·
      refine ⟨4450502834920543733871787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5934003779894058311829049 4450502834920543733871787)
      ·
        refine ⟨6675754252380815600807681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4450502834920543733871787 6675754252380815600807681)
        ·
          refine ⟨5006815689285611700605761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6675754252380815600807681 5006815689285611700605761)
          ·
            refine ⟨3755111766964208775454321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006815689285611700605761 3755111766964208775454321)
            ·
              refine ⟨2816333825223156581590741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755111766964208775454321 2816333825223156581590741)
              ·
                refine ⟨66007824028667732381033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2816333825223156581590741 66007824028667732381033)
                ·
                  rfl

theorem cell22_1735422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_1735422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735422 prefixEnd_1735422 := by exact prefixLift 1735422
  have htrace : WordTrace (prefixWord ++ tailWord_1735422) baseStart_1735422 baseEnd_1735422 := by
    simpa [prefixWord, tailWord_1735422, baseEnd_1735422] using wordTrace_append hprefix tailTrace_1735422
  have hstable : (prefixWord ++ tailWord_1735422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735422).length < 2 ^ (prefixWord ++ tailWord_1735422).sum := by decide
  have hdescent : baseEnd_1735422 < baseStart_1735422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735426 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1735426 : Nat := 118140960795 + 1735426 * 2 ^ 59
def prefixEnd_1735426 : Nat := 4983230072969 + 3 ^ 40 * 1735426 * 2
def baseEnd_1735426 : Nat := 594071785539754914329285

theorem tailTrace_1735426 : CollatzResearch.WordTrace tailWord_1735426 prefixEnd_1735426 594071785539754914329285 := by
  unfold tailWord_1735426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15824046552713866002330533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42197457473903642672881421 15824046552713866002330533)
  ·
    refine ⟨2967008728633849875436975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15824046552713866002330533 2967008728633849875436975)
    ·
      refine ⟨4450513092950774813155463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967008728633849875436975 4450513092950774813155463)
      ·
        refine ⟨6675769639426162219733195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4450513092950774813155463 6675769639426162219733195)
        ·
          refine ⟨10013654459139243329599793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6675769639426162219733195 10013654459139243329599793)
          ·
            refine ⟨7510240844354432497199845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10013654459139243329599793 7510240844354432497199845)
            ·
              refine ⟨1408170158316456093224971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7510240844354432497199845 1408170158316456093224971)
              ·
                refine ⟨2112255237474684139837457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408170158316456093224971 2112255237474684139837457)
                ·
                  refine ⟨1584191428106013104878093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2112255237474684139837457 1584191428106013104878093)
                  ·
                    refine ⟨594071785539754914329285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1584191428106013104878093 594071785539754914329285)
                    ·
                      rfl

theorem cell22_1735426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1735426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735426 prefixEnd_1735426 := by exact prefixLift 1735426
  have htrace : WordTrace (prefixWord ++ tailWord_1735426) baseStart_1735426 baseEnd_1735426 := by
    simpa [prefixWord, tailWord_1735426, baseEnd_1735426] using wordTrace_append hprefix tailTrace_1735426
  have hstable : (prefixWord ++ tailWord_1735426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735426).length < 2 ^ (prefixWord ++ tailWord_1735426).sum := by decide
  have hdescent : baseEnd_1735426 < baseStart_1735426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735480 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_1735480 : Nat := 118140960795 + 1735480 * 2 ^ 59
def prefixEnd_1735480 : Nat := 4983230072969 + 3 ^ 40 * 1735480 * 2
def baseEnd_1735480 : Nat := 594090270843316773479119

theorem tailTrace_1735480 : CollatzResearch.WordTrace tailWord_1735480 prefixEnd_1735480 594090270843316773479119 := by
  unfold tailWord_1735480
  simp only [CollatzResearch.WordTrace]
  refine ⟨31649077876329915615893947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42198770501773220821191929 31649077876329915615893947)
  ·
    refine ⟨47473616814494873423840921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31649077876329915615893947 47473616814494873423840921)
    ·
      refine ⟨35605212610871155067880691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47473616814494873423840921 35605212610871155067880691)
      ·
        refine ⟨53407818916306732601821037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35605212610871155067880691 53407818916306732601821037)
        ·
          refine ⟨20027932093615024725682889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53407818916306732601821037 20027932093615024725682889)
          ·
            refine ⟨15020949070211268544262167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20027932093615024725682889 15020949070211268544262167)
            ·
              refine ⟨22531423605316902816393251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15020949070211268544262167 22531423605316902816393251)
              ·
                refine ⟨33797135407975354224589877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22531423605316902816393251 33797135407975354224589877)
                ·
                  refine ⟨3168481444497689458555301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33797135407975354224589877 3168481444497689458555301)
                  ·
                    refine ⟨594090270843316773479119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3168481444497689458555301 594090270843316773479119)
                    ·
                      rfl

theorem cell22_1735480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_1735480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735480 prefixEnd_1735480 := by exact prefixLift 1735480
  have htrace : WordTrace (prefixWord ++ tailWord_1735480) baseStart_1735480 baseEnd_1735480 := by
    simpa [prefixWord, tailWord_1735480, baseEnd_1735480] using wordTrace_append hprefix tailTrace_1735480
  have hstable : (prefixWord ++ tailWord_1735480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735480).length < 2 ^ (prefixWord ++ tailWord_1735480).sum := by decide
  have hdescent : baseEnd_1735480 < baseStart_1735480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735482 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_1735482 : Nat := 118140960795 + 1735482 * 2 ^ 59
def prefixEnd_1735482 : Nat := 4983230072969 + 3 ^ 40 * 1735482 * 2
def baseEnd_1735482 : Nat := 594090955484189434929113

theorem tailTrace_1735482 : CollatzResearch.WordTrace tailWord_1735482 prefixEnd_1735482 594090955484189434929113 := by
  unfold tailWord_1735482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15824557174663146393340175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42198819132435057048907133 15824557174663146393340175)
  ·
    refine ⟨23736835761994719590010263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15824557174663146393340175 23736835761994719590010263)
    ·
      refine ⟨35605253642992079385015395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23736835761994719590010263 35605253642992079385015395)
      ·
        refine ⟨53407880464488119077523093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35605253642992079385015395 53407880464488119077523093)
        ·
          refine ⟨2503494396772880581758895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53407880464488119077523093 2503494396772880581758895)
          ·
            refine ⟨3755241595159320872638343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503494396772880581758895 3755241595159320872638343)
            ·
              refine ⟨5632862392738981308957515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755241595159320872638343 5632862392738981308957515)
              ·
                refine ⟨8449293589108471963436273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632862392738981308957515 8449293589108471963436273)
                ·
                  refine ⟨6336970191831353972577205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8449293589108471963436273 6336970191831353972577205)
                  ·
                    refine ⟨594090955484189434929113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6336970191831353972577205 594090955484189434929113)
                    ·
                      rfl

theorem cell22_1735482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_1735482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735482 prefixEnd_1735482 := by exact prefixLift 1735482
  have htrace : WordTrace (prefixWord ++ tailWord_1735482) baseStart_1735482 baseEnd_1735482 := by
    simpa [prefixWord, tailWord_1735482, baseEnd_1735482] using wordTrace_append hprefix tailTrace_1735482
  have hstable : (prefixWord ++ tailWord_1735482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735482).length < 2 ^ (prefixWord ++ tailWord_1735482).sum := by decide
  have hdescent : baseEnd_1735482 < baseStart_1735482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735514 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_1735514 : Nat := 118140960795 + 1735514 * 2 ^ 59
def prefixEnd_1735514 : Nat := 4983230072969 + 3 ^ 40 * 1735514 * 2
def baseEnd_1735514 : Nat := 594101909738152018129015

theorem tailTrace_1735514 : CollatzResearch.WordTrace tailWord_1735514 prefixEnd_1735514 594101909738152018129015 := by
  unfold tailWord_1735514
  simp only [CollatzResearch.WordTrace]
  refine ⟨15824848958634163759631399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42199597223024436692350397 15824848958634163759631399)
  ·
    refine ⟨23737273437951245639447099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15824848958634163759631399 23737273437951245639447099)
    ·
      refine ⟨35605910156926868459170649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23737273437951245639447099 35605910156926868459170649)
      ·
        refine ⟨26704432617695151344377987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35605910156926868459170649 26704432617695151344377987)
        ·
          refine ⟨40056648926542727016566981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26704432617695151344377987 40056648926542727016566981)
          ·
            refine ⟨7510621673726761315606309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40056648926542727016566981 7510621673726761315606309)
            ·
              refine ⟨1408241563823767746676183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7510621673726761315606309 1408241563823767746676183)
              ·
                refine ⟨2112362345735651620014275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408241563823767746676183 2112362345735651620014275)
                ·
                  refine ⟨3168543518603477430021413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112362345735651620014275 3168543518603477430021413)
                  ·
                    refine ⟨594101909738152018129015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3168543518603477430021413 594101909738152018129015)
                    ·
                      rfl

theorem cell22_1735514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_1735514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735514 prefixEnd_1735514 := by exact prefixLift 1735514
  have htrace : WordTrace (prefixWord ++ tailWord_1735514) baseStart_1735514 baseEnd_1735514 := by
    simpa [prefixWord, tailWord_1735514, baseEnd_1735514] using wordTrace_append hprefix tailTrace_1735514
  have hstable : (prefixWord ++ tailWord_1735514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735514).length < 2 ^ (prefixWord ++ tailWord_1735514).sum := by decide
  have hdescent : baseEnd_1735514 < baseStart_1735514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735555 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 2, 7]
def baseStart_1735555 : Nat := 118140960795 + 1735555 * 2 ^ 59
def prefixEnd_1735555 : Nat := 4983230072969 + 3 ^ 40 * 1735555 * 2
def baseEnd_1735555 : Nat := 594115944876041577853889

theorem tailTrace_1735555 : CollatzResearch.WordTrace tailWord_1735555 prefixEnd_1735555 594115944876041577853889 := by
  unfold tailWord_1735555
  simp only [CollatzResearch.WordTrace]
  refine ⟨63300891227388119040768119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42200594151592079360512079 63300891227388119040768119)
  ·
    refine ⟨94951336841082178561152179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63300891227388119040768119 94951336841082178561152179)
    ·
      refine ⟨142427005261623267841728269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94951336841082178561152179 142427005261623267841728269)
      ·
        refine ⟨53410126973108725440648101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142427005261623267841728269 53410126973108725440648101)
        ·
          refine ⟨10014398807457886020121519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53410126973108725440648101 10014398807457886020121519)
          ·
            refine ⟨15021598211186829030182279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10014398807457886020121519 15021598211186829030182279)
            ·
              refine ⟨22532397316780243545273419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15021598211186829030182279 22532397316780243545273419)
              ·
                refine ⟨33798595975170365317910129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22532397316780243545273419 33798595975170365317910129)
                ·
                  refine ⟨25348946981377773988432597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33798595975170365317910129 25348946981377773988432597)
                  ·
                    refine ⟨594115944876041577853889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25348946981377773988432597 594115944876041577853889)
                    ·
                      rfl

theorem cell22_1735555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_1735555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735555 prefixEnd_1735555 := by exact prefixLift 1735555
  have htrace : WordTrace (prefixWord ++ tailWord_1735555) baseStart_1735555 baseEnd_1735555 := by
    simpa [prefixWord, tailWord_1735555, baseEnd_1735555] using wordTrace_append hprefix tailTrace_1735555
  have hstable : (prefixWord ++ tailWord_1735555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735555).length < 2 ^ (prefixWord ++ tailWord_1735555).sum := by decide
  have hdescent : baseEnd_1735555 < baseStart_1735555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735557 : List Nat := [1, 3, 1, 1, 3, 3, 4, 6]
def baseStart_1735557 : Nat := 118140960795 + 1735557 * 2 ^ 59
def prefixEnd_1735557 : Nat := 4983230072969 + 3 ^ 40 * 1735557 * 2
def baseEnd_1735557 : Nat := 66012958835212693255987

theorem tailTrace_1735557 : CollatzResearch.WordTrace tailWord_1735557 prefixEnd_1735557 66012958835212693255987 := by
  unfold tailWord_1735557
  simp only [CollatzResearch.WordTrace]
  refine ⟨63300964173380873382340925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42200642782253915588227283 63300964173380873382340925)
  ·
    refine ⟨23737861565017827518377847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63300964173380873382340925 23737861565017827518377847)
    ·
      refine ⟨35606792347526741277566771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23737861565017827518377847 35606792347526741277566771)
      ·
        refine ⟨53410188521290111916350157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35606792347526741277566771 53410188521290111916350157)
        ·
          refine ⟨20028820695483791968631309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53410188521290111916350157 20028820695483791968631309)
          ·
            refine ⟨7510807760806421988236741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20028820695483791968631309 7510807760806421988236741)
            ·
              refine ⟨1408276455151204122794389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7510807760806421988236741 1408276455151204122794389)
              ·
                refine ⟨66012958835212693255987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1408276455151204122794389 66012958835212693255987)
                ·
                  rfl

theorem cell22_1735557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 6].length) (baseStart_1735557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735557 prefixEnd_1735557 := by exact prefixLift 1735557
  have htrace : WordTrace (prefixWord ++ tailWord_1735557) baseStart_1735557 baseEnd_1735557 := by
    simpa [prefixWord, tailWord_1735557, baseEnd_1735557] using wordTrace_append hprefix tailTrace_1735557
  have hstable : (prefixWord ++ tailWord_1735557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735557).length < 2 ^ (prefixWord ++ tailWord_1735557).sum := by decide
  have hdescent : baseEnd_1735557 < baseStart_1735557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735681 : List Nat := [1, 2, 4, 1, 2, 3, 2, 3, 4]
def baseStart_1735681 : Nat := 118140960795 + 1735681 * 2 ^ 59
def prefixEnd_1735681 : Nat := 4983230072969 + 3 ^ 40 * 1735681 * 2
def baseEnd_1735681 : Nat := 198053025750339749734501

theorem tailTrace_1735681 : CollatzResearch.WordTrace tailWord_1735681 prefixEnd_1735681 198053025750339749734501 := by
  unfold tailWord_1735681
  simp only [CollatzResearch.WordTrace]
  refine ⟨63305486824931642559854897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42203657883287761706569931 63305486824931642559854897)
  ·
    refine ⟨47479115118698731919891173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63305486824931642559854897 47479115118698731919891173)
    ·
      refine ⟨8902334084756012234979595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47479115118698731919891173 8902334084756012234979595)
      ·
        refine ⟨13353501127134018352469393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8902334084756012234979595 13353501127134018352469393)
        ·
          refine ⟨10015125845350513764352045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13353501127134018352469393 10015125845350513764352045)
          ·
            refine ⟨3755672192006442661632017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10015125845350513764352045 3755672192006442661632017)
            ·
              refine ⟨2816754144004831996224013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755672192006442661632017 2816754144004831996224013)
              ·
                refine ⟨1056282804001811998584005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2816754144004831996224013 1056282804001811998584005)
                ·
                  refine ⟨198053025750339749734501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056282804001811998584005 198053025750339749734501)
                  ·
                    rfl

theorem cell22_1735681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_1735681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735681 prefixEnd_1735681 := by exact prefixLift 1735681
  have htrace : WordTrace (prefixWord ++ tailWord_1735681) baseStart_1735681 baseEnd_1735681 := by
    simpa [prefixWord, tailWord_1735681, baseEnd_1735681] using wordTrace_append hprefix tailTrace_1735681
  have hstable : (prefixWord ++ tailWord_1735681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735681).length < 2 ^ (prefixWord ++ tailWord_1735681).sum := by decide
  have hdescent : baseEnd_1735681 < baseStart_1735681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735692 : List Nat := [2, 2, 1, 2, 3, 3, 9]
def baseStart_1735692 : Nat := 118140960795 + 1735692 * 2 ^ 59
def prefixEnd_1735692 : Nat := 4983230072969 + 3 ^ 40 * 1735692 * 2
def baseEnd_1735692 : Nat := 22006031213919218043647

theorem tailTrace_1735692 : CollatzResearch.WordTrace tailWord_1735692 prefixEnd_1735692 22006031213919218043647 := by
  unfold tailWord_1735692
  simp only [CollatzResearch.WordTrace]
  refine ⟨31652944013945895719252665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42203925351927860959003553 31652944013945895719252665)
  ·
    refine ⟨23739708010459421789439499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31652944013945895719252665 23739708010459421789439499)
    ·
      refine ⟨35609562015689132684159249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23739708010459421789439499 35609562015689132684159249)
      ·
        refine ⟨26707171511766849513119437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35609562015689132684159249 26707171511766849513119437)
        ·
          refine ⟨10015189316912568567419789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26707171511766849513119437 10015189316912568567419789)
          ·
            refine ⟨3755695993842213212782421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10015189316912568567419789 3755695993842213212782421)
            ·
              refine ⟨22006031213919218043647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3755695993842213212782421 22006031213919218043647)
              ·
                rfl

theorem cell22_1735692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 9].length) (baseStart_1735692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735692 prefixEnd_1735692 := by exact prefixLift 1735692
  have htrace : WordTrace (prefixWord ++ tailWord_1735692) baseStart_1735692 baseEnd_1735692 := by
    simpa [prefixWord, tailWord_1735692, baseEnd_1735692] using wordTrace_append hprefix tailTrace_1735692
  have hstable : (prefixWord ++ tailWord_1735692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735692).length < 2 ^ (prefixWord ++ tailWord_1735692).sum := by decide
  have hdescent : baseEnd_1735692 < baseStart_1735692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735713 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 2, 3]
def baseStart_1735713 : Nat := 118140960795 + 1735713 * 2 ^ 59
def prefixEnd_1735713 : Nat := 4983230072969 + 3 ^ 40 * 1735713 * 2
def baseEnd_1735713 : Nat := 594170031504981832403405

theorem tailTrace_1735713 : CollatzResearch.WordTrace tailWord_1735713 prefixEnd_1735713 594170031504981832403405 := by
  unfold tailWord_1735713
  simp only [CollatzResearch.WordTrace]
  refine ⟨63306653960815712025019793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42204435973877141350013195 63306653960815712025019793)
  ·
    refine ⟨47479990470611784018764845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63306653960815712025019793 47479990470611784018764845)
    ·
      refine ⟨17804996426479419007036817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47479990470611784018764845 17804996426479419007036817)
      ·
        refine ⟨13353747319859564255277613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17804996426479419007036817 13353747319859564255277613)
        ·
          refine ⟨5007655244947336595729105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13353747319859564255277613 5007655244947336595729105)
          ·
            refine ⟨3755741433710502446796829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5007655244947336595729105 3755741433710502446796829)
            ·
              refine ⟨1408403037641438417548811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3755741433710502446796829 1408403037641438417548811)
              ·
                refine ⟨2112604556462157626323217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408403037641438417548811 2112604556462157626323217)
                ·
                  refine ⟨1584453417346618219742413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2112604556462157626323217 1584453417346618219742413)
                  ·
                    refine ⟨594170031504981832403405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1584453417346618219742413 594170031504981832403405)
                    ·
                      rfl

theorem cell22_1735713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_1735713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735713 prefixEnd_1735713 := by exact prefixLift 1735713
  have htrace : WordTrace (prefixWord ++ tailWord_1735713) baseStart_1735713 baseEnd_1735713 := by
    simpa [prefixWord, tailWord_1735713, baseEnd_1735713] using wordTrace_append hprefix tailTrace_1735713
  have hstable : (prefixWord ++ tailWord_1735713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735713).length < 2 ^ (prefixWord ++ tailWord_1735713).sum := by decide
  have hdescent : baseEnd_1735713 < baseStart_1735713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735724 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_1735724 : Nat := 118140960795 + 1735724 * 2 ^ 59
def prefixEnd_1735724 : Nat := 4983230072969 + 3 ^ 40 * 1735724 * 2
def baseEnd_1735724 : Nat := 594173797029781470378371

theorem tailTrace_1735724 : CollatzResearch.WordTrace tailWord_1735724 prefixEnd_1735724 594173797029781470378371 := by
  unfold tailWord_1735724
  simp only [CollatzResearch.WordTrace]
  refine ⟨31653527581887930451835113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42204703442517240602446817 31653527581887930451835113)
  ·
    refine ⟨23740145686415947838876335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31653527581887930451835113 23740145686415947838876335)
    ·
      refine ⟨35610218529623921758314503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23740145686415947838876335 35610218529623921758314503)
      ·
        refine ⟨53415327794435882637471755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35610218529623921758314503 53415327794435882637471755)
        ·
          refine ⟨80122991691653823956207633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53415327794435882637471755 80122991691653823956207633)
          ·
            refine ⟨60092243768740367967155725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80122991691653823956207633 60092243768740367967155725)
            ·
              refine ⟨22534591413277637987683397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60092243768740367967155725 22534591413277637987683397)
              ·
                refine ⟨4225235889989557122690637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22534591413277637987683397 4225235889989557122690637)
                ·
                  refine ⟨1584463458746083921008989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4225235889989557122690637 1584463458746083921008989)
                  ·
                    refine ⟨594173797029781470378371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1584463458746083921008989 594173797029781470378371)
                    ·
                      rfl

theorem cell22_1735724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_1735724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735724 prefixEnd_1735724 := by exact prefixLift 1735724
  have htrace : WordTrace (prefixWord ++ tailWord_1735724) baseStart_1735724 baseEnd_1735724 := by
    simpa [prefixWord, tailWord_1735724, baseEnd_1735724] using wordTrace_append hprefix tailTrace_1735724
  have hstable : (prefixWord ++ tailWord_1735724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735724).length < 2 ^ (prefixWord ++ tailWord_1735724).sum := by decide
  have hdescent : baseEnd_1735724 < baseStart_1735724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735767 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1735767 : Nat := 118140960795 + 1735767 * 2 ^ 59
def prefixEnd_1735767 : Nat := 4983230072969 + 3 ^ 40 * 1735767 * 2
def baseEnd_1735767 : Nat := 594188516808543691553239

theorem tailTrace_1735767 : CollatzResearch.WordTrace tailWord_1735767 prefixEnd_1735767 594188516808543691553239 := by
  unfold tailWord_1735767
  simp only [CollatzResearch.WordTrace]
  refine ⟨63308623502620079247485555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42205749001746719498323703 63308623502620079247485555)
  ·
    refine ⟨94962935253930118871228333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63308623502620079247485555 94962935253930118871228333)
    ·
      refine ⟨35611100720223794576710625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94962935253930118871228333 35611100720223794576710625)
      ·
        refine ⟨26708325540167845932532969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35611100720223794576710625 26708325540167845932532969)
        ·
          refine ⟨20031244155125884449399727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26708325540167845932532969 20031244155125884449399727)
          ·
            refine ⟨30046866232688826674099591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20031244155125884449399727 30046866232688826674099591)
            ·
              refine ⟨45070299349033240011149387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30046866232688826674099591 45070299349033240011149387)
              ·
                refine ⟨67605449023549860016724081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45070299349033240011149387 67605449023549860016724081)
                ·
                  refine ⟨50704086767662395012543061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67605449023549860016724081 50704086767662395012543061)
                  ·
                    refine ⟨594188516808543691553239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50704086767662395012543061 594188516808543691553239)
                    ·
                      rfl

theorem cell22_1735767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1735767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735767 prefixEnd_1735767 := by exact prefixLift 1735767
  have htrace : WordTrace (prefixWord ++ tailWord_1735767) baseStart_1735767 baseEnd_1735767 := by
    simpa [prefixWord, tailWord_1735767, baseEnd_1735767] using wordTrace_append hprefix tailTrace_1735767
  have hstable : (prefixWord ++ tailWord_1735767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735767).length < 2 ^ (prefixWord ++ tailWord_1735767).sum := by decide
  have hdescent : baseEnd_1735767 < baseStart_1735767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735831 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 1, 5]
def baseStart_1735831 : Nat := 118140960795 + 1735831 * 2 ^ 59
def prefixEnd_1735831 : Nat := 4983230072969 + 3 ^ 40 * 1735831 * 2
def baseEnd_1735831 : Nat := 594210425316468857953043

theorem tailTrace_1735831 : CollatzResearch.WordTrace tailWord_1735831 prefixEnd_1735831 594210425316468857953043 := by
  unfold tailWord_1735831
  simp only [CollatzResearch.WordTrace]
  refine ⟨63310957774388218177815347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42207305182925478785210231 63310957774388218177815347)
  ·
    refine ⟨94966436661582327266723021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63310957774388218177815347 94966436661582327266723021)
    ·
      refine ⟨35612413748093372725021133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94966436661582327266723021 35612413748093372725021133)
      ·
        refine ⟨13354655155535014771882925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35612413748093372725021133 13354655155535014771882925)
        ·
          refine ⟨5007995683325630539456097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13354655155535014771882925 5007995683325630539456097)
          ·
            refine ⟨3755996762494222904592073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5007995683325630539456097 3755996762494222904592073)
            ·
              refine ⟨2816997571870667178444055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755996762494222904592073 2816997571870667178444055)
              ·
                refine ⟨4225496357806000767666083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816997571870667178444055 4225496357806000767666083)
                ·
                  refine ⟨6338244536709001151499125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225496357806000767666083 6338244536709001151499125)
                  ·
                    refine ⟨594210425316468857953043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6338244536709001151499125 594210425316468857953043)
                    ·
                      rfl

theorem cell22_1735831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_1735831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735831 prefixEnd_1735831 := by exact prefixLift 1735831
  have htrace : WordTrace (prefixWord ++ tailWord_1735831) baseStart_1735831 baseEnd_1735831 := by
    simpa [prefixWord, tailWord_1735831, baseEnd_1735831] using wordTrace_append hprefix tailTrace_1735831
  have hstable : (prefixWord ++ tailWord_1735831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735831).length < 2 ^ (prefixWord ++ tailWord_1735831).sum := by decide
  have hdescent : baseEnd_1735831 < baseStart_1735831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735850 : List Nat := [3, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_1735850 : Nat := 118140960795 + 1735850 * 2 ^ 59
def prefixEnd_1735850 : Nat := 4983230072969 + 3 ^ 40 * 1735850 * 2
def baseEnd_1735850 : Nat := 198072309801586380575995

theorem tailTrace_1735850 : CollatzResearch.WordTrace tailWord_1735850 prefixEnd_1735850 198072309801586380575995 := by
  unfold tailWord_1735850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15827912690329846105689251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42207767174212922948504669 15827912690329846105689251)
  ·
    refine ⟨23741869035494769158533877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15827912690329846105689251 23741869035494769158533877)
    ·
      refine ⟨2225800222077634608612551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23741869035494769158533877 2225800222077634608612551)
      ·
        refine ⟨3338700333116451912918827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225800222077634608612551 3338700333116451912918827)
        ·
          refine ⟨5008050499674677869378241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338700333116451912918827 5008050499674677869378241)
          ·
            refine ⟨3756037874756008402033681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5008050499674677869378241 3756037874756008402033681)
            ·
              refine ⟨2817028406067006301525261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3756037874756008402033681 2817028406067006301525261)
              ·
                refine ⟨1056385652275127363071973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2817028406067006301525261 1056385652275127363071973)
                ·
                  refine ⟨198072309801586380575995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056385652275127363071973 198072309801586380575995)
                  ·
                    rfl

theorem cell22_1735850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_1735850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735850 prefixEnd_1735850 := by exact prefixLift 1735850
  have htrace : WordTrace (prefixWord ++ tailWord_1735850) baseStart_1735850 baseEnd_1735850 := by
    simpa [prefixWord, tailWord_1735850, baseEnd_1735850] using wordTrace_append hprefix tailTrace_1735850
  have hstable : (prefixWord ++ tailWord_1735850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735850).length < 2 ^ (prefixWord ++ tailWord_1735850).sum := by decide
  have hdescent : baseEnd_1735850 < baseStart_1735850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735893 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_1735893 : Nat := 118140960795 + 1735893 * 2 ^ 59
def prefixEnd_1735893 : Nat := 4983230072969 + 3 ^ 40 * 1735893 * 2
def baseEnd_1735893 : Nat := 594231649183521362902853

theorem tailTrace_1735893 : CollatzResearch.WordTrace tailWord_1735893 prefixEnd_1735893 594231649183521362902853 := by
  unfold tailWord_1735893
  simp only [CollatzResearch.WordTrace]
  refine ⟨63313219100163602766572333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42208812733442401844381555 63313219100163602766572333)
  ·
    refine ⟨23742457162561351037464625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63313219100163602766572333 23742457162561351037464625)
    ·
      refine ⟨17806842871921013278098469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23742457162561351037464625 17806842871921013278098469)
      ·
        refine ⟨3338783038485189989643463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17806842871921013278098469 3338783038485189989643463)
        ·
          refine ⟨5008174557727784984465195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338783038485189989643463 5008174557727784984465195)
          ·
            refine ⟨7512261836591677476697793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008174557727784984465195 7512261836591677476697793)
            ·
              refine ⟨5634196377443758107523345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7512261836591677476697793 5634196377443758107523345)
              ·
                refine ⟨4225647283082818580642509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5634196377443758107523345 4225647283082818580642509)
                ·
                  refine ⟨1584617731156056967740941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4225647283082818580642509 1584617731156056967740941)
                  ·
                    refine ⟨594231649183521362902853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1584617731156056967740941 594231649183521362902853)
                    ·
                      rfl

theorem cell22_1735893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_1735893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735893 prefixEnd_1735893 := by exact prefixLift 1735893
  have htrace : WordTrace (prefixWord ++ tailWord_1735893) baseStart_1735893 baseEnd_1735893 := by
    simpa [prefixWord, tailWord_1735893, baseEnd_1735893] using wordTrace_append hprefix tailTrace_1735893
  have hstable : (prefixWord ++ tailWord_1735893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735893).length < 2 ^ (prefixWord ++ tailWord_1735893).sum := by decide
  have hdescent : baseEnd_1735893 < baseStart_1735893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735940 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 5]
def baseStart_1735940 : Nat := 118140960795 + 1735940 * 2 ^ 59
def prefixEnd_1735940 : Nat := 4983230072969 + 3 ^ 40 * 1735940 * 2
def baseEnd_1735940 : Nat := 198082579414676302325903

theorem tailTrace_1735940 : CollatzResearch.WordTrace tailWord_1735940 prefixEnd_1735940 198082579414676302325903 := by
  unfold tailWord_1735940
  simp only [CollatzResearch.WordTrace]
  refine ⟨31657466665496664896766637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42209955553995553195688849 31657466665496664896766637)
  ·
    refine ⟨11871549999561249336287489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31657466665496664896766637 11871549999561249336287489)
    ·
      refine ⟨8903662499670937002215617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11871549999561249336287489 8903662499670937002215617)
      ·
        refine ⟨6677746874753202751661713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8903662499670937002215617 6677746874753202751661713)
        ·
          refine ⟨5008310156064902063746285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6677746874753202751661713 5008310156064902063746285)
          ·
            refine ⟨1878116308524338273904857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5008310156064902063746285 1878116308524338273904857)
            ·
              refine ⟨1408587231393253705428643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878116308524338273904857 1408587231393253705428643)
              ·
                refine ⟨2112880847089880558142965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408587231393253705428643 2112880847089880558142965)
                ·
                  refine ⟨198082579414676302325903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2112880847089880558142965 198082579414676302325903)
                  ·
                    rfl

theorem cell22_1735940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_1735940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735940 prefixEnd_1735940 := by exact prefixLift 1735940
  have htrace : WordTrace (prefixWord ++ tailWord_1735940) baseStart_1735940 baseEnd_1735940 := by
    simpa [prefixWord, tailWord_1735940, baseEnd_1735940] using wordTrace_append hprefix tailTrace_1735940
  have hstable : (prefixWord ++ tailWord_1735940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735940).length < 2 ^ (prefixWord ++ tailWord_1735940).sum := by decide
  have hdescent : baseEnd_1735940 < baseStart_1735940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735985 : List Nat := [1, 2, 2, 3, 3, 1, 4, 2, 4]
def baseStart_1735985 : Nat := 118140960795 + 1735985 * 2 ^ 59
def prefixEnd_1735985 : Nat := 4983230072969 + 3 ^ 40 * 1735985 * 2
def baseEnd_1735985 : Nat := 198087714221221263200857

theorem tailTrace_1735985 : CollatzResearch.WordTrace tailWord_1735985 prefixEnd_1735985 198087714221221263200857 := by
  unfold tailWord_1735985
  simp only [CollatzResearch.WordTrace]
  refine ⟨63316574615830302478921409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42211049743886868319280939 63316574615830302478921409)
  ·
    refine ⟨47487430961872726859191057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63316574615830302478921409 47487430961872726859191057)
    ·
      refine ⟨35615573221404545144393293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47487430961872726859191057 35615573221404545144393293)
      ·
        refine ⟨13355839958026704429147485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35615573221404545144393293 13355839958026704429147485)
        ·
          refine ⟨5008439984260014160930307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13355839958026704429147485 5008439984260014160930307)
          ·
            refine ⟨7512659976390021241395461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008439984260014160930307 7512659976390021241395461)
            ·
              refine ⟨1408623745573128982761649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7512659976390021241395461 1408623745573128982761649)
              ·
                refine ⟨1056467809179846737071237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408623745573128982761649 1056467809179846737071237)
                ·
                  refine ⟨198087714221221263200857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056467809179846737071237 198087714221221263200857)
                  ·
                    rfl

theorem cell22_1735985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_1735985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735985 prefixEnd_1735985 := by exact prefixLift 1735985
  have htrace : WordTrace (prefixWord ++ tailWord_1735985) baseStart_1735985 baseEnd_1735985 := by
    simpa [prefixWord, tailWord_1735985, baseEnd_1735985] using wordTrace_append hprefix tailTrace_1735985
  have hstable : (prefixWord ++ tailWord_1735985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735985).length < 2 ^ (prefixWord ++ tailWord_1735985).sum := by decide
  have hdescent : baseEnd_1735985 < baseStart_1735985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735996 : List Nat := [2, 2, 2, 2, 1, 3, 3, 7]
def baseStart_1735996 : Nat := 118140960795 + 1735996 * 2 ^ 59
def prefixEnd_1735996 : Nat := 4983230072969 + 3 ^ 40 * 1735996 * 2
def baseEnd_1735996 : Nat := 66029656465384825286393

theorem tailTrace_1735996 : CollatzResearch.WordTrace tailWord_1735996 prefixEnd_1735996 66029656465384825286393 := by
  unfold tailWord_1735996
  simp only [CollatzResearch.WordTrace]
  refine ⟨31658487909395225678785921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42211317212526967571714561 31658487909395225678785921)
  ·
    refine ⟨23743865932046419259089441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31658487909395225678785921 23743865932046419259089441)
    ·
      refine ⟨17807899449034814444317081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23743865932046419259089441 17807899449034814444317081)
      ·
        refine ⟨13355924586776110833237811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17807899449034814444317081 13355924586776110833237811)
        ·
          refine ⟨20033886880164166249856717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13355924586776110833237811 20033886880164166249856717)
          ·
            refine ⟨7512707580061562343696269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20033886880164166249856717 7512707580061562343696269)
            ·
              refine ⟨2817265342523085878886101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7512707580061562343696269 2817265342523085878886101)
              ·
                refine ⟨66029656465384825286393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2817265342523085878886101 66029656465384825286393)
                ·
                  rfl

theorem cell22_1735996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 7].length) (baseStart_1735996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1735996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1735996 prefixEnd_1735996 := by exact prefixLift 1735996
  have htrace : WordTrace (prefixWord ++ tailWord_1735996) baseStart_1735996 baseEnd_1735996 := by
    simpa [prefixWord, tailWord_1735996, baseEnd_1735996] using wordTrace_append hprefix tailTrace_1735996
  have hstable : (prefixWord ++ tailWord_1735996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735996).length < 2 ^ (prefixWord ++ tailWord_1735996).sum := by decide
  have hdescent : baseEnd_1735996 < baseStart_1735996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736041 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 5]
def baseStart_1736041 : Nat := 118140960795 + 1736041 * 2 ^ 59
def prefixEnd_1736041 : Nat := 4983230072969 + 3 ^ 40 * 1736041 * 2
def baseEnd_1736041 : Nat := 198094104202699436734133

theorem tailTrace_1736041 : CollatzResearch.WordTrace tailWord_1736041 prefixEnd_1736041 198094104202699436734133 := by
  unfold tailWord_1736041
  simp only [CollatzResearch.WordTrace]
  refine ⟨63318617103627424042959977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42212411402418282695306651 63318617103627424042959977)
  ·
    refine ⟨47488962827720568032219983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63318617103627424042959977 47488962827720568032219983)
    ·
      refine ⟨71233444241580852048329975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47488962827720568032219983 71233444241580852048329975)
      ·
        refine ⟨106850166362371278072494963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71233444241580852048329975 106850166362371278072494963)
        ·
          refine ⟨160275249543556917108742445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106850166362371278072494963 160275249543556917108742445)
          ·
            refine ⟨60103218578833843915778417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160275249543556917108742445 60103218578833843915778417)
            ·
              refine ⟨45077413934125382936833813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60103218578833843915778417 45077413934125382936833813)
              ·
                refine ⟨2113003778162127325164085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45077413934125382936833813 2113003778162127325164085)
                ·
                  refine ⟨198094104202699436734133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113003778162127325164085 198094104202699436734133)
                  ·
                    rfl

theorem cell22_1736041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_1736041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736041 prefixEnd_1736041 := by exact prefixLift 1736041
  have htrace : WordTrace (prefixWord ++ tailWord_1736041) baseStart_1736041 baseEnd_1736041 := by
    simpa [prefixWord, tailWord_1736041, baseEnd_1736041] using wordTrace_append hprefix tailTrace_1736041
  have hstable : (prefixWord ++ tailWord_1736041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736041).length < 2 ^ (prefixWord ++ tailWord_1736041).sum := by decide
  have hdescent : baseEnd_1736041 < baseStart_1736041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736045 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_1736045 : Nat := 118140960795 + 1736045 * 2 ^ 59
def prefixEnd_1736045 : Nat := 4983230072969 + 3 ^ 40 * 1736045 * 2
def baseEnd_1736045 : Nat := 594283681889843633102387

theorem tailTrace_1736045 : CollatzResearch.WordTrace tailWord_1736045 prefixEnd_1736045 594283681889843633102387 := by
  unfold tailWord_1736045
  simp only [CollatzResearch.WordTrace]
  refine ⟨63318762995612932726105589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42212508663741955150737059 63318762995612932726105589)
  ·
    refine ⟨5936134030838712443072399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63318762995612932726105589 5936134030838712443072399)
    ·
      refine ⟨8904201046258068664608599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5936134030838712443072399 8904201046258068664608599)
      ·
        refine ⟨13356301569387102996912899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8904201046258068664608599 13356301569387102996912899)
        ·
          refine ⟨20034452354080654495369349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13356301569387102996912899 20034452354080654495369349)
          ·
            refine ⟨3756459816390122717881753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20034452354080654495369349 3756459816390122717881753)
            ·
              refine ⟨2817344862292592038411315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3756459816390122717881753 2817344862292592038411315)
              ·
                refine ⟨4226017293438888057616973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817344862292592038411315 4226017293438888057616973)
                ·
                  refine ⟨1584756485039583021606365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4226017293438888057616973 1584756485039583021606365)
                  ·
                    refine ⟨594283681889843633102387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1584756485039583021606365 594283681889843633102387)
                    ·
                      rfl

theorem cell22_1736045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_1736045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736045 prefixEnd_1736045 := by exact prefixLift 1736045
  have htrace : WordTrace (prefixWord ++ tailWord_1736045) baseStart_1736045 baseEnd_1736045 := by
    simpa [prefixWord, tailWord_1736045, baseEnd_1736045] using wordTrace_append hprefix tailTrace_1736045
  have hstable : (prefixWord ++ tailWord_1736045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736045).length < 2 ^ (prefixWord ++ tailWord_1736045).sum := by decide
  have hdescent : baseEnd_1736045 < baseStart_1736045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736101 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1736101 : Nat := 118140960795 + 1736101 * 2 ^ 59
def prefixEnd_1736101 : Nat := 4983230072969 + 3 ^ 40 * 1736101 * 2
def baseEnd_1736101 : Nat := 594302851834278153702215

theorem tailTrace_1736101 : CollatzResearch.WordTrace tailWord_1736101 prefixEnd_1736101 594302851834278153702215 := by
  unfold tailWord_1736101
  simp only [CollatzResearch.WordTrace]
  refine ⟨63320805483410054290144157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42213870322273369526762771 63320805483410054290144157)
  ·
    refine ⟨23745302056278770358804059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63320805483410054290144157 23745302056278770358804059)
    ·
      refine ⟨35617953084418155538206089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23745302056278770358804059 35617953084418155538206089)
      ·
        refine ⟨26713464813313616653654567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35617953084418155538206089 26713464813313616653654567)
        ·
          refine ⟨40070197219970424980481851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26713464813313616653654567 40070197219970424980481851)
          ·
            refine ⟨60105295829955637470722777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40070197219970424980481851 60105295829955637470722777)
            ·
              refine ⟨45078971872466728103042083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60105295829955637470722777 45078971872466728103042083)
              ·
                refine ⟨67618457808700092154563125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45078971872466728103042083 67618457808700092154563125)
                ·
                  refine ⟨6339230419565633639490293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67618457808700092154563125 6339230419565633639490293)
                  ·
                    refine ⟨594302851834278153702215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6339230419565633639490293 594302851834278153702215)
                    ·
                      rfl

theorem cell22_1736101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1736101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736101 prefixEnd_1736101 := by exact prefixLift 1736101
  have htrace : WordTrace (prefixWord ++ tailWord_1736101) baseStart_1736101 baseEnd_1736101 := by
    simpa [prefixWord, tailWord_1736101, baseEnd_1736101] using wordTrace_append hprefix tailTrace_1736101
  have hstable : (prefixWord ++ tailWord_1736101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736101).length < 2 ^ (prefixWord ++ tailWord_1736101).sum := by decide
  have hdescent : baseEnd_1736101 < baseStart_1736101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736131 : List Nat := [1, 1, 1, 3, 1, 1, 6, 8]
def baseStart_1736131 : Nat := 118140960795 + 1736131 * 2 ^ 59
def prefixEnd_1736131 : Nat := 4983230072969 + 3 ^ 40 * 1736131 * 2
def baseEnd_1736131 : Nat := 66034791271929786161347

theorem tailTrace_1736131 : CollatzResearch.WordTrace tailWord_1736131 prefixEnd_1736131 66034791271929786161347 := by
  unfold tailWord_1736131
  simp only [CollatzResearch.WordTrace]
  refine ⟨63321899673301369413736247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42214599782200912942490831 63321899673301369413736247)
  ·
    refine ⟨94982849509952054120604371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63321899673301369413736247 94982849509952054120604371)
    ·
      refine ⟨142474274264928081180906557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94982849509952054120604371 142474274264928081180906557)
      ·
        refine ⟨53427852849348030442839959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142474274264928081180906557 53427852849348030442839959)
        ·
          refine ⟨80141779274022045664259939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53427852849348030442839959 80141779274022045664259939)
          ·
            refine ⟨120212668911033068496389909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80141779274022045664259939 120212668911033068496389909)
            ·
              refine ⟨5634968855204675085768277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120212668911033068496389909 5634968855204675085768277)
              ·
                refine ⟨66034791271929786161347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5634968855204675085768277 66034791271929786161347)
                ·
                  rfl

theorem cell22_1736131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 8].length) (baseStart_1736131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736131 prefixEnd_1736131 := by exact prefixLift 1736131
  have htrace : WordTrace (prefixWord ++ tailWord_1736131) baseStart_1736131 baseEnd_1736131 := by
    simpa [prefixWord, tailWord_1736131, baseEnd_1736131] using wordTrace_append hprefix tailTrace_1736131
  have hstable : (prefixWord ++ tailWord_1736131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736131).length < 2 ^ (prefixWord ++ tailWord_1736131).sum := by decide
  have hdescent : baseEnd_1736131 < baseStart_1736131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736148 : List Nat := [2, 4, 1, 2, 3, 10]
def baseStart_1736148 : Nat := 118140960795 + 1736148 * 2 ^ 59
def prefixEnd_1736148 : Nat := 4983230072969 + 3 ^ 40 * 1736148 * 2
def baseEnd_1736148 : Nat := 7337270875244267873791

theorem tailTrace_1736148 : CollatzResearch.WordTrace tailWord_1736148 prefixEnd_1736148 7337270875244267873791 := by
  unfold tailWord_1736148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31661259857119890658552549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42215013142826520878070065 31661259857119890658552549)
  ·
    refine ⟨5936486223209979498478603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31661259857119890658552549 5936486223209979498478603)
    ·
      refine ⟨8904729334814969247717905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5936486223209979498478603 8904729334814969247717905)
      ·
        refine ⟨6678547001111226935788429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8904729334814969247717905 6678547001111226935788429)
        ·
          refine ⟨2504455125416710100920661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6678547001111226935788429 2504455125416710100920661)
          ·
            refine ⟨7337270875244267873791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2504455125416710100920661 7337270875244267873791)
            ·
              rfl

theorem cell22_1736148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 10].length) (baseStart_1736148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736148 prefixEnd_1736148 := by exact prefixLift 1736148
  have htrace : WordTrace (prefixWord ++ tailWord_1736148) baseStart_1736148 baseEnd_1736148 := by
    simpa [prefixWord, tailWord_1736148, baseEnd_1736148] using wordTrace_append hprefix tailTrace_1736148
  have hstable : (prefixWord ++ tailWord_1736148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736148).length < 2 ^ (prefixWord ++ tailWord_1736148).sum := by decide
  have hdescent : baseEnd_1736148 < baseStart_1736148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736165 : List Nat := [1, 3, 1, 5, 1, 3, 1, 7]
def baseStart_1736165 : Nat := 118140960795 + 1736165 * 2 ^ 59
def prefixEnd_1736165 : Nat := 4983230072969 + 3 ^ 40 * 1736165 * 2
def baseEnd_1736165 : Nat := 66036084482467035566891

theorem tailTrace_1736165 : CollatzResearch.WordTrace tailWord_1736165 prefixEnd_1736165 66036084482467035566891 := by
  unfold tailWord_1736165
  simp only [CollatzResearch.WordTrace]
  refine ⟨63323139755178193220473949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42215426503452128813649299 63323139755178193220473949)
  ·
    refine ⟨23746177408191822457677731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63323139755178193220473949 23746177408191822457677731)
    ·
      refine ⟨35619266112287733686516597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23746177408191822457677731 35619266112287733686516597)
      ·
        refine ⟨3339306198026975033110931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35619266112287733686516597 3339306198026975033110931)
        ·
          refine ⟨5008959297040462549666397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339306198026975033110931 5008959297040462549666397)
          ·
            refine ⟨1878359736390173456124899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5008959297040462549666397 1878359736390173456124899)
            ·
              refine ⟨2817539604585260184187349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878359736390173456124899 2817539604585260184187349)
              ·
                refine ⟨66036084482467035566891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2817539604585260184187349 66036084482467035566891)
                ·
                  rfl

theorem cell22_1736165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 7].length) (baseStart_1736165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736165 prefixEnd_1736165 := by exact prefixLift 1736165
  have htrace : WordTrace (prefixWord ++ tailWord_1736165) baseStart_1736165 baseEnd_1736165 := by
    simpa [prefixWord, tailWord_1736165, baseEnd_1736165] using wordTrace_append hprefix tailTrace_1736165
  have hstable : (prefixWord ++ tailWord_1736165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736165).length < 2 ^ (prefixWord ++ tailWord_1736165).sum := by decide
  have hdescent : baseEnd_1736165 < baseStart_1736165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736223 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 5, 4]
def baseStart_1736223 : Nat := 118140960795 + 1736223 * 2 ^ 59
def prefixEnd_1736223 : Nat := 4983230072969 + 3 ^ 40 * 1736223 * 2
def baseEnd_1736223 : Nat := 594344614927510502151841

theorem tailTrace_1736223 : CollatzResearch.WordTrace tailWord_1736223 prefixEnd_1736223 594344614927510502151841 := by
  unfold tailWord_1736223
  simp only [CollatzResearch.WordTrace]
  refine ⟨63325255188968069126085323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42216836792645379417390215 63325255188968069126085323)
  ·
    refine ⟨94987882783452103689127985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63325255188968069126085323 94987882783452103689127985)
    ·
      refine ⟨71240912087589077766845989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94987882783452103689127985 71240912087589077766845989)
      ·
        refine ⟨13357671016422952081283623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71240912087589077766845989 13357671016422952081283623)
        ·
          refine ⟨20036506524634428121925435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13357671016422952081283623 20036506524634428121925435)
          ·
            refine ⟨30054759786951642182888153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20036506524634428121925435 30054759786951642182888153)
            ·
              refine ⟨22541069840213731637166115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30054759786951642182888153 22541069840213731637166115)
              ·
                refine ⟨33811604760320597455749173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22541069840213731637166115 33811604760320597455749173)
                ·
                  refine ⟨3169837946280056011476485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33811604760320597455749173 3169837946280056011476485)
                  ·
                    refine ⟨594344614927510502151841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3169837946280056011476485 594344614927510502151841)
                    ·
                      rfl

theorem cell22_1736223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_1736223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736223 prefixEnd_1736223 := by exact prefixLift 1736223
  have htrace : WordTrace (prefixWord ++ tailWord_1736223) baseStart_1736223 baseEnd_1736223 := by
    simpa [prefixWord, tailWord_1736223, baseEnd_1736223] using wordTrace_append hprefix tailTrace_1736223
  have hstable : (prefixWord ++ tailWord_1736223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736223).length < 2 ^ (prefixWord ++ tailWord_1736223).sum := by decide
  have hdescent : baseEnd_1736223 < baseStart_1736223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736227 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 5]
def baseStart_1736227 : Nat := 118140960795 + 1736227 * 2 ^ 59
def prefixEnd_1736227 : Nat := 4983230072969 + 3 ^ 40 * 1736227 * 2
def baseEnd_1736227 : Nat := 198115328069751941683943

theorem tailTrace_1736227 : CollatzResearch.WordTrace tailWord_1736227 prefixEnd_1736227 198115328069751941683943 := by
  unfold tailWord_1736227
  simp only [CollatzResearch.WordTrace]
  refine ⟨63325401080953577809230935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42216934053969051872820623 63325401080953577809230935)
  ·
    refine ⟨94988101621430366713846403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63325401080953577809230935 94988101621430366713846403)
    ·
      refine ⟨142482152432145550070769605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94988101621430366713846403 142482152432145550070769605)
      ·
        refine ⟨26715403581027290638269301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142482152432145550070769605 26715403581027290638269301)
        ·
          refine ⟨2504569085721308497337747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26715403581027290638269301 2504569085721308497337747)
          ·
            refine ⟨3756853628581962746006621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504569085721308497337747 3756853628581962746006621)
            ·
              refine ⟨1408820110718236029752483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3756853628581962746006621 1408820110718236029752483)
              ·
                refine ⟨2113230166077354044628725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408820110718236029752483 2113230166077354044628725)
                ·
                  refine ⟨198115328069751941683943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113230166077354044628725 198115328069751941683943)
                  ·
                    rfl

theorem cell22_1736227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 5].length) (baseStart_1736227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736227 prefixEnd_1736227 := by exact prefixLift 1736227
  have htrace : WordTrace (prefixWord ++ tailWord_1736227) baseStart_1736227 baseEnd_1736227 := by
    simpa [prefixWord, tailWord_1736227, baseEnd_1736227] using wordTrace_append hprefix tailTrace_1736227
  have hstable : (prefixWord ++ tailWord_1736227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736227).length < 2 ^ (prefixWord ++ tailWord_1736227).sum := by decide
  have hdescent : baseEnd_1736227 < baseStart_1736227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736272 : List Nat := [2, 1, 1, 1, 1, 3, 7, 2, 4]
def baseStart_1736272 : Nat := 118140960795 + 1736272 * 2 ^ 59
def prefixEnd_1736272 : Nat := 4983230072969 + 3 ^ 40 * 1736272 * 2
def baseEnd_1736272 : Nat := 198120462876296902558897

theorem tailTrace_1736272 : CollatzResearch.WordTrace tailWord_1736272 prefixEnd_1736272 198120462876296902558897 := by
  unfold tailWord_1736272
  simp only [CollatzResearch.WordTrace]
  refine ⟨31663521182895275247309535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42218028243860366996412713 31663521182895275247309535)
  ·
    refine ⟨47495281774342912870964303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31663521182895275247309535 47495281774342912870964303)
    ·
      refine ⟨71242922661514369306446455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47495281774342912870964303 71242922661514369306446455)
      ·
        refine ⟨106864383992271553959669683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71242922661514369306446455 106864383992271553959669683)
        ·
          refine ⟨160296575988407330939504525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106864383992271553959669683 160296575988407330939504525)
          ·
            refine ⟨60111215995652749102314197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160296575988407330939504525 60111215995652749102314197)
            ·
              refine ⟨1408856624898111307085489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60111215995652749102314197 1408856624898111307085489)
              ·
                refine ⟨1056642468673583480314117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408856624898111307085489 1056642468673583480314117)
                ·
                  refine ⟨198120462876296902558897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056642468673583480314117 198120462876296902558897)
                  ·
                    rfl

theorem cell22_1736272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_1736272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736272 prefixEnd_1736272 := by exact prefixLift 1736272
  have htrace : WordTrace (prefixWord ++ tailWord_1736272) baseStart_1736272 baseEnd_1736272 := by
    simpa [prefixWord, tailWord_1736272, baseEnd_1736272] using wordTrace_append hprefix tailTrace_1736272
  have hstable : (prefixWord ++ tailWord_1736272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736272).length < 2 ^ (prefixWord ++ tailWord_1736272).sum := by decide
  have hdescent : baseEnd_1736272 < baseStart_1736272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736278 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1736278 : Nat := 118140960795 + 1736278 * 2 ^ 59
def prefixEnd_1736278 : Nat := 4983230072969 + 3 ^ 40 * 1736278 * 2
def baseEnd_1736278 : Nat := 198121147517169564008891

theorem tailTrace_1736278 : CollatzResearch.WordTrace tailWord_1736278 prefixEnd_1736278 198121147517169564008891 := by
  unfold tailWord_1736278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957953825235550844958593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42218174135845875679558325 3957953825235550844958593)
  ·
    refine ⟨2968465368926663133718945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3957953825235550844958593 2968465368926663133718945)
    ·
      refine ⟨2226349026694997350289209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2968465368926663133718945 2226349026694997350289209)
      ·
        refine ⟨1669761770021248012716907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2226349026694997350289209 1669761770021248012716907)
        ·
          refine ⟨2504642655031872019075361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669761770021248012716907 2504642655031872019075361)
          ·
            refine ⟨1878481991273904014306521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2504642655031872019075361 1878481991273904014306521)
            ·
              refine ⟨1408861493455428010729891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878481991273904014306521 1408861493455428010729891)
              ·
                refine ⟨2113292240183142016094837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408861493455428010729891 2113292240183142016094837)
                ·
                  refine ⟨198121147517169564008891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113292240183142016094837 198121147517169564008891)
                  ·
                    rfl

theorem cell22_1736278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1736278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736278 prefixEnd_1736278 := by exact prefixLift 1736278
  have htrace : WordTrace (prefixWord ++ tailWord_1736278) baseStart_1736278 baseEnd_1736278 := by
    simpa [prefixWord, tailWord_1736278, baseEnd_1736278] using wordTrace_append hprefix tailTrace_1736278
  have hstable : (prefixWord ++ tailWord_1736278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736278).length < 2 ^ (prefixWord ++ tailWord_1736278).sum := by decide
  have hdescent : baseEnd_1736278 < baseStart_1736278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736330 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1736330 : Nat := 118140960795 + 1736330 * 2 ^ 59
def prefixEnd_1736330 : Nat := 4983230072969 + 3 ^ 40 * 1736330 * 2
def baseEnd_1736330 : Nat := 594381243214197889726513

theorem tailTrace_1736330 : CollatzResearch.WordTrace tailWord_1736330 prefixEnd_1736330 594381243214197889726513 := by
  unfold tailWord_1736330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15832289449895106600057611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42219438533053617600153629 15832289449895106600057611)
  ·
    refine ⟨23748434174842659900086417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15832289449895106600057611 23748434174842659900086417)
    ·
      refine ⟨17811325631131994925064813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23748434174842659900086417 17811325631131994925064813)
      ·
        refine ⟨6679247111674498096899305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17811325631131994925064813 6679247111674498096899305)
        ·
          refine ⟨5009435333755873572674479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6679247111674498096899305 5009435333755873572674479)
          ·
            refine ⟨7514153000633810359011719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009435333755873572674479 7514153000633810359011719)
            ·
              refine ⟨11271229500950715538517579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514153000633810359011719 11271229500950715538517579)
              ·
                refine ⟨16906844251426073307776369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271229500950715538517579 16906844251426073307776369)
                ·
                  refine ⟨12680133188569554980832277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16906844251426073307776369 12680133188569554980832277)
                  ·
                    refine ⟨594381243214197889726513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12680133188569554980832277 594381243214197889726513)
                    ·
                      rfl

theorem cell22_1736330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1736330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736330 prefixEnd_1736330 := by exact prefixLift 1736330
  have htrace : WordTrace (prefixWord ++ tailWord_1736330) baseStart_1736330 baseEnd_1736330 := by
    simpa [prefixWord, tailWord_1736330, baseEnd_1736330] using wordTrace_append hprefix tailTrace_1736330
  have hstable : (prefixWord ++ tailWord_1736330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736330).length < 2 ^ (prefixWord ++ tailWord_1736330).sum := by decide
  have hdescent : baseEnd_1736330 < baseStart_1736330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736420 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1736420 : Nat := 118140960795 + 1736420 * 2 ^ 59
def prefixEnd_1736420 : Nat := 4983230072969 + 3 ^ 40 * 1736420 * 2
def baseEnd_1736420 : Nat := 594412052053467654976237

theorem tailTrace_1736420 : CollatzResearch.WordTrace tailWord_1736420 prefixEnd_1736420 594412052053467654976237 := by
  unfold tailWord_1736420
  simp only [CollatzResearch.WordTrace]
  refine ⟨31666220184627185885503357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42221626912836247847337809 31666220184627185885503357)
  ·
    refine ⟨11874832569235194707063759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31666220184627185885503357 11874832569235194707063759)
    ·
      refine ⟨17812248853852792060595639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11874832569235194707063759 17812248853852792060595639)
      ·
        refine ⟨26718373280779188090893459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17812248853852792060595639 26718373280779188090893459)
        ·
          refine ⟨40077559921168782136340189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26718373280779188090893459 40077559921168782136340189)
          ·
            refine ⟨15029084970438293301127571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40077559921168782136340189 15029084970438293301127571)
            ·
              refine ⟨22543627455657439951691357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15029084970438293301127571 22543627455657439951691357)
              ·
                refine ⟨8453860295871539981884259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22543627455657439951691357 8453860295871539981884259)
                ·
                  refine ⟨12680790443807309972826389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8453860295871539981884259 12680790443807309972826389)
                  ·
                    refine ⟨594412052053467654976237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12680790443807309972826389 594412052053467654976237)
                    ·
                      rfl

theorem cell22_1736420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1736420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736420 prefixEnd_1736420 := by exact prefixLift 1736420
  have htrace : WordTrace (prefixWord ++ tailWord_1736420) baseStart_1736420 baseEnd_1736420 := by
    simpa [prefixWord, tailWord_1736420, baseEnd_1736420] using wordTrace_append hprefix tailTrace_1736420
  have hstable : (prefixWord ++ tailWord_1736420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736420).length < 2 ^ (prefixWord ++ tailWord_1736420).sum := by decide
  have hdescent : baseEnd_1736420 < baseStart_1736420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736424 : List Nat := [2, 1, 4, 1, 3, 1, 3, 3, 4]
def baseStart_1736424 : Nat := 118140960795 + 1736424 * 2 ^ 59
def prefixEnd_1736424 : Nat := 4983230072969 + 3 ^ 40 * 1736424 * 2
def baseEnd_1736424 : Nat := 198137807111737659292075

theorem tailTrace_1736424 : CollatzResearch.WordTrace tailWord_1736424 prefixEnd_1736424 198137807111737659292075 := by
  unfold tailWord_1736424
  simp only [CollatzResearch.WordTrace]
  refine ⟨31666293130619940227076163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42221724174159920302768217 31666293130619940227076163)
  ·
    refine ⟨47499439695929910340614245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31666293130619940227076163 47499439695929910340614245)
    ·
      refine ⟨8906144942986858188865171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47499439695929910340614245 8906144942986858188865171)
      ·
        refine ⟨13359217414480287283297757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8906144942986858188865171 13359217414480287283297757)
        ·
          refine ⟨5009706530430107731236659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13359217414480287283297757 5009706530430107731236659)
          ·
            refine ⟨7514559795645161596854989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009706530430107731236659 7514559795645161596854989)
            ·
              refine ⟨2817959923366935598820621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7514559795645161596854989 2817959923366935598820621)
              ·
                refine ⟨1056734971262600849557733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2817959923366935598820621 1056734971262600849557733)
                ·
                  refine ⟨198137807111737659292075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056734971262600849557733 198137807111737659292075)
                  ·
                    rfl

theorem cell22_1736424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_1736424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736424 prefixEnd_1736424 := by exact prefixLift 1736424
  have htrace : WordTrace (prefixWord ++ tailWord_1736424) baseStart_1736424 baseEnd_1736424 := by
    simpa [prefixWord, tailWord_1736424, baseEnd_1736424] using wordTrace_append hprefix tailTrace_1736424
  have hstable : (prefixWord ++ tailWord_1736424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736424).length < 2 ^ (prefixWord ++ tailWord_1736424).sum := by decide
  have hdescent : baseEnd_1736424 < baseStart_1736424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736452 : List Nat := [2, 3, 2, 2, 1, 3, 2, 7]
def baseStart_1736452 : Nat := 118140960795 + 1736452 * 2 ^ 59
def prefixEnd_1736452 : Nat := 4983230072969 + 3 ^ 40 * 1736452 * 2
def baseEnd_1736452 : Nat := 66047000700825582019571

theorem tailTrace_1736452 : CollatzResearch.WordTrace tailWord_1736452 prefixEnd_1736452 66047000700825582019571 := by
  unfold tailWord_1736452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31666803752569220618085805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42222405003425627490781073 31666803752569220618085805)
  ·
    refine ⟨11875051407213457731782177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31666803752569220618085805 11875051407213457731782177)
    ·
      refine ⟨8906288555410093298836633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11875051407213457731782177 8906288555410093298836633)
      ·
        refine ⟨6679716416557569974127475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8906288555410093298836633 6679716416557569974127475)
        ·
          refine ⟨10019574624836354961191213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6679716416557569974127475 10019574624836354961191213)
          ·
            refine ⟨3757340484313633110446705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10019574624836354961191213 3757340484313633110446705)
            ·
              refine ⟨2818005363235224832835029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3757340484313633110446705 2818005363235224832835029)
              ·
                refine ⟨66047000700825582019571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2818005363235224832835029 66047000700825582019571)
                ·
                  rfl

theorem cell22_1736452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 7].length) (baseStart_1736452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736452 prefixEnd_1736452 := by exact prefixLift 1736452
  have htrace : WordTrace (prefixWord ++ tailWord_1736452) baseStart_1736452 baseEnd_1736452 := by
    simpa [prefixWord, tailWord_1736452, baseEnd_1736452] using wordTrace_append hprefix tailTrace_1736452
  have hstable : (prefixWord ++ tailWord_1736452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736452).length < 2 ^ (prefixWord ++ tailWord_1736452).sum := by decide
  have hdescent : baseEnd_1736452 < baseStart_1736452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736495 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 4, 5]
def baseStart_1736495 : Nat := 118140960795 + 1736495 * 2 ^ 59
def prefixEnd_1736495 : Nat := 4983230072969 + 3 ^ 40 * 1736495 * 2
def baseEnd_1736495 : Nat := 594437726086192459351007

theorem tailTrace_1736495 : CollatzResearch.WordTrace tailWord_1736495 prefixEnd_1736495 594437726086192459351007 := by
  unfold tailWord_1736495
  simp only [CollatzResearch.WordTrace]
  refine ⟨63335175843982659579986939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42223450562655106386657959 63335175843982659579986939)
  ·
    refine ⟨95002763765973989369980409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63335175843982659579986939 95002763765973989369980409)
    ·
      refine ⟨71252072824480492027485307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95002763765973989369980409 71252072824480492027485307)
      ·
        refine ⟨106878109236720738041227961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71252072824480492027485307 106878109236720738041227961)
        ·
          refine ⟨80158581927540553530920971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106878109236720738041227961 80158581927540553530920971)
          ·
            refine ⟨120237872891310830296381457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80158581927540553530920971 120237872891310830296381457)
            ·
              refine ⟨90178404668483122722286093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120237872891310830296381457 90178404668483122722286093)
              ·
                refine ⟨33816901750681171020857285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90178404668483122722286093 33816901750681171020857285)
                ·
                  refine ⟨6340669078252719566410741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33816901750681171020857285 6340669078252719566410741)
                  ·
                    refine ⟨594437726086192459351007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6340669078252719566410741 594437726086192459351007)
                    ·
                      rfl

theorem cell22_1736495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_1736495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736495 prefixEnd_1736495 := by exact prefixLift 1736495
  have htrace : WordTrace (prefixWord ++ tailWord_1736495) baseStart_1736495 baseEnd_1736495 := by
    simpa [prefixWord, tailWord_1736495, baseEnd_1736495] using wordTrace_append hprefix tailTrace_1736495
  have hstable : (prefixWord ++ tailWord_1736495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736495).length < 2 ^ (prefixWord ++ tailWord_1736495).sum := by decide
  have hdescent : baseEnd_1736495 < baseStart_1736495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736497 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 5]
def baseStart_1736497 : Nat := 118140960795 + 1736497 * 2 ^ 59
def prefixEnd_1736497 : Nat := 4983230072969 + 3 ^ 40 * 1736497 * 2
def baseEnd_1736497 : Nat := 198146136909021706933667

theorem tailTrace_1736497 : CollatzResearch.WordTrace tailWord_1736497 prefixEnd_1736497 198146136909021706933667 := by
  unfold tailWord_1736497
  simp only [CollatzResearch.WordTrace]
  refine ⟨63335248789975413921559745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42223499193316942614373163 63335248789975413921559745)
  ·
    refine ⟨47501436592481560441169809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63335248789975413921559745 47501436592481560441169809)
    ·
      refine ⟨35626077444361170330877357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47501436592481560441169809 35626077444361170330877357)
      ·
        refine ⟨13359779041635438874079009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35626077444361170330877357 13359779041635438874079009)
        ·
          refine ⟨10019834281226579155559257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13359779041635438874079009 10019834281226579155559257)
          ·
            refine ⟨7514875710919934366669443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10019834281226579155559257 7514875710919934366669443)
            ·
              refine ⟨11272313566379901550004165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514875710919934366669443 11272313566379901550004165)
              ·
                refine ⟨2113558793696231540625781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11272313566379901550004165 2113558793696231540625781)
                ·
                  refine ⟨198146136909021706933667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113558793696231540625781 198146136909021706933667)
                  ·
                    rfl

theorem cell22_1736497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_1736497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736497 prefixEnd_1736497 := by exact prefixLift 1736497
  have htrace : WordTrace (prefixWord ++ tailWord_1736497) baseStart_1736497 baseEnd_1736497 := by
    simpa [prefixWord, tailWord_1736497, baseEnd_1736497] using wordTrace_append hprefix tailTrace_1736497
  have hstable : (prefixWord ++ tailWord_1736497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736497).length < 2 ^ (prefixWord ++ tailWord_1736497).sum := by decide
  have hdescent : baseEnd_1736497 < baseStart_1736497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736518 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1736518 : Nat := 118140960795 + 1736518 * 2 ^ 59
def prefixEnd_1736518 : Nat := 4983230072969 + 3 ^ 40 * 1736518 * 2
def baseEnd_1736518 : Nat := 594445599456228066025937

theorem tailTrace_1736518 : CollatzResearch.WordTrace tailWord_1736518 prefixEnd_1736518 594445599456228066025937 := by
  unfold tailWord_1736518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979250460090604203377319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42224009815266223005382805 1979250460090604203377319)
  ·
    refine ⟨2968875690135906305065979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1979250460090604203377319 2968875690135906305065979)
    ·
      refine ⟨4453313535203859457598969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968875690135906305065979 4453313535203859457598969)
      ·
        refine ⟨3339985151402894593199227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4453313535203859457598969 3339985151402894593199227)
        ·
          refine ⟨5009977727104341889798841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339985151402894593199227 5009977727104341889798841)
          ·
            refine ⟨3757483295328256417349131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5009977727104341889798841 3757483295328256417349131)
            ·
              refine ⟨5636224942992384626023697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757483295328256417349131 5636224942992384626023697)
              ·
                refine ⟨4227168707244288469517773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636224942992384626023697 4227168707244288469517773)
                ·
                  refine ⟨1585188265216608176069165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4227168707244288469517773 1585188265216608176069165)
                  ·
                    refine ⟨594445599456228066025937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1585188265216608176069165 594445599456228066025937)
                    ·
                      rfl

theorem cell22_1736518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1736518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736518 prefixEnd_1736518 := by exact prefixLift 1736518
  have htrace : WordTrace (prefixWord ++ tailWord_1736518) baseStart_1736518 baseEnd_1736518 := by
    simpa [prefixWord, tailWord_1736518, baseEnd_1736518] using wordTrace_append hprefix tailTrace_1736518
  have hstable : (prefixWord ++ tailWord_1736518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736518).length < 2 ^ (prefixWord ++ tailWord_1736518).sum := by decide
  have hdescent : baseEnd_1736518 < baseStart_1736518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736544 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_1736544 : Nat := 118140960795 + 1736544 * 2 ^ 59
def prefixEnd_1736544 : Nat := 4983230072969 + 3 ^ 40 * 1736544 * 2
def baseEnd_1736544 : Nat := 594454499787572664875857

theorem tailTrace_1736544 : CollatzResearch.WordTrace tailWord_1736544 prefixEnd_1736544 594454499787572664875857 := by
  unfold tailWord_1736544
  simp only [CollatzResearch.WordTrace]
  refine ⟨31668481510402570474260343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42224642013870093965680457 31668481510402570474260343)
  ·
    refine ⟨47502722265603855711390515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31668481510402570474260343 47502722265603855711390515)
    ·
      refine ⟨71254083398405783567085773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47502722265603855711390515 71254083398405783567085773)
      ·
        refine ⟨26720281274402168837657165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71254083398405783567085773 26720281274402168837657165)
        ·
          refine ⟨10020105477900813314121437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26720281274402168837657165 10020105477900813314121437)
          ·
            refine ⟨3757539554212804992795539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10020105477900813314121437 3757539554212804992795539)
            ·
              refine ⟨5636309331319207489193309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757539554212804992795539 5636309331319207489193309)
              ·
                refine ⟨2113615999244702808447491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5636309331319207489193309 2113615999244702808447491)
                ·
                  refine ⟨3170423998867054212671237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113615999244702808447491 3170423998867054212671237)
                  ·
                    refine ⟨594454499787572664875857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3170423998867054212671237 594454499787572664875857)
                    ·
                      rfl

theorem cell22_1736544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_1736544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736544 prefixEnd_1736544 := by exact prefixLift 1736544
  have htrace : WordTrace (prefixWord ++ tailWord_1736544) baseStart_1736544 baseEnd_1736544 := by
    simpa [prefixWord, tailWord_1736544, baseEnd_1736544] using wordTrace_append hprefix tailTrace_1736544
  have hstable : (prefixWord ++ tailWord_1736544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736544).length < 2 ^ (prefixWord ++ tailWord_1736544).sum := by decide
  have hdescent : baseEnd_1736544 < baseStart_1736544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736557 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1736557 : Nat := 118140960795 + 1736557 * 2 ^ 59
def prefixEnd_1736557 : Nat := 4983230072969 + 3 ^ 40 * 1736557 * 2
def baseEnd_1736557 : Nat := 594458949953244964300817

theorem tailTrace_1736557 : CollatzResearch.WordTrace tailWord_1736557 prefixEnd_1736557 594458949953244964300817 := by
  unfold tailWord_1736557
  simp only [CollatzResearch.WordTrace]
  refine ⟨63337437169758044168743925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42224958113172029445829283 63337437169758044168743925)
  ·
    refine ⟨5937884734664816640819743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63337437169758044168743925 5937884734664816640819743)
    ·
      refine ⟨8906827101997224961229615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5937884734664816640819743 8906827101997224961229615)
      ·
        refine ⟨13360240652995837441844423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8906827101997224961229615 13360240652995837441844423)
        ·
          refine ⟨20040360979493756162766635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13360240652995837441844423 20040360979493756162766635)
          ·
            refine ⟨30060541469240634244149953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20040360979493756162766635 30060541469240634244149953)
            ·
              refine ⟨22545406101930475683112465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30060541469240634244149953 22545406101930475683112465)
              ·
                refine ⟨16909054576447856762334349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22545406101930475683112465 16909054576447856762334349)
                ·
                  refine ⟨6340895466167946285875381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16909054576447856762334349 6340895466167946285875381)
                  ·
                    refine ⟨594458949953244964300817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6340895466167946285875381 594458949953244964300817)
                    ·
                      rfl

theorem cell22_1736557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1736557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736557 prefixEnd_1736557 := by exact prefixLift 1736557
  have htrace : WordTrace (prefixWord ++ tailWord_1736557) baseStart_1736557 baseEnd_1736557 := by
    simpa [prefixWord, tailWord_1736557, baseEnd_1736557] using wordTrace_append hprefix tailTrace_1736557
  have hstable : (prefixWord ++ tailWord_1736557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736557).length < 2 ^ (prefixWord ++ tailWord_1736557).sum := by decide
  have hdescent : baseEnd_1736557 < baseStart_1736557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736604 : List Nat := [2, 2, 3, 3, 1, 3, 8]
def baseStart_1736604 : Nat := 118140960795 + 1736604 * 2 ^ 59
def prefixEnd_1736604 : Nat := 4983230072969 + 3 ^ 40 * 1736604 * 2
def baseEnd_1736604 : Nat := 22017594037546389199099

theorem tailTrace_1736604 : CollatzResearch.WordTrace tailWord_1736604 prefixEnd_1736604 22017594037546389199099 := by
  unfold tailWord_1736604
  simp only [CollatzResearch.WordTrace]
  refine ⟨31669575700293885597852433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42226100933725180797136577 31669575700293885597852433)
  ·
    refine ⟨23752181775220414198389325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31669575700293885597852433 23752181775220414198389325)
    ·
      refine ⟨8907068165707655324395997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23752181775220414198389325 8907068165707655324395997)
      ·
        refine ⟨3340150562140370746648499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8907068165707655324395997 3340150562140370746648499)
        ·
          refine ⟨5010225843210556119972749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340150562140370746648499 5010225843210556119972749)
          ·
            refine ⟨1878834691203958544989781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5010225843210556119972749 1878834691203958544989781)
            ·
              refine ⟨22017594037546389199099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1878834691203958544989781 22017594037546389199099)
              ·
                rfl

theorem cell22_1736604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 8].length) (baseStart_1736604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736604 prefixEnd_1736604 := by exact prefixLift 1736604
  have htrace : WordTrace (prefixWord ++ tailWord_1736604) baseStart_1736604 baseEnd_1736604 := by
    simpa [prefixWord, tailWord_1736604, baseEnd_1736604] using wordTrace_append hprefix tailTrace_1736604
  have hstable : (prefixWord ++ tailWord_1736604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736604).length < 2 ^ (prefixWord ++ tailWord_1736604).sum := by decide
  have hdescent : baseEnd_1736604 < baseStart_1736604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736647 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1736647 : Nat := 118140960795 + 1736647 * 2 ^ 59
def prefixEnd_1736647 : Nat := 4983230072969 + 3 ^ 40 * 1736647 * 2
def baseEnd_1736647 : Nat := 594489758792514729550541

theorem tailTrace_1736647 : CollatzResearch.WordTrace tailWord_1736647 prefixEnd_1736647 594489758792514729550541 := by
  unfold tailWord_1736647
  simp only [CollatzResearch.WordTrace]
  refine ⟨63340719739431989539520195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42227146492954659693013463 63340719739431989539520195)
  ·
    refine ⟨95011079609147984309280293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63340719739431989539520195 95011079609147984309280293)
    ·
      refine ⟨17814577426715247057990055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95011079609147984309280293 17814577426715247057990055)
      ·
        refine ⟨26721866140072870586985083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17814577426715247057990055 26721866140072870586985083)
        ·
          refine ⟨40082799210109305880477625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26721866140072870586985083 40082799210109305880477625)
          ·
            refine ⟨30062099407581979410358219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40082799210109305880477625 30062099407581979410358219)
            ·
              refine ⟨45093149111372969115537329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30062099407581979410358219 45093149111372969115537329)
              ·
                refine ⟨33819861833529726836652997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45093149111372969115537329 33819861833529726836652997)
                ·
                  refine ⟨6341224093786823781872437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33819861833529726836652997 6341224093786823781872437)
                  ·
                    refine ⟨594489758792514729550541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6341224093786823781872437 594489758792514729550541)
                    ·
                      rfl

theorem cell22_1736647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1736647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736647 prefixEnd_1736647 := by exact prefixLift 1736647
  have htrace : WordTrace (prefixWord ++ tailWord_1736647) baseStart_1736647 baseEnd_1736647 := by
    simpa [prefixWord, tailWord_1736647, baseEnd_1736647] using wordTrace_append hprefix tailTrace_1736647
  have hstable : (prefixWord ++ tailWord_1736647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736647).length < 2 ^ (prefixWord ++ tailWord_1736647).sum := by decide
  have hdescent : baseEnd_1736647 < baseStart_1736647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736666 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_1736666 : Nat := 118140960795 + 1736666 * 2 ^ 59
def prefixEnd_1736666 : Nat := 4983230072969 + 3 ^ 40 * 1736666 * 2
def baseEnd_1736666 : Nat := 198165420960268337775161

theorem tailTrace_1736666 : CollatzResearch.WordTrace tailWord_1736666 prefixEnd_1736666 198165420960268337775161 := by
  unfold tailWord_1736666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15835353181590788946115463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42227608484242103856307901 15835353181590788946115463)
  ·
    refine ⟨23753029772386183419173195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15835353181590788946115463 23753029772386183419173195)
    ·
      refine ⟨35629544658579275128759793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23753029772386183419173195 35629544658579275128759793)
      ·
        refine ⟨26722158493934456346569845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35629544658579275128759793 26722158493934456346569845)
        ·
          refine ⟨2505202358806355282490923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26722158493934456346569845 2505202358806355282490923)
          ·
            refine ⟨3757803538209532923736385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505202358806355282490923 3757803538209532923736385)
            ·
              refine ⟨2818352653657149692802289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3757803538209532923736385 2818352653657149692802289)
              ·
                refine ⟨2113764490242862269601717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2818352653657149692802289 2113764490242862269601717)
                ·
                  refine ⟨198165420960268337775161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113764490242862269601717 198165420960268337775161)
                  ·
                    rfl

theorem cell22_1736666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_1736666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736666 prefixEnd_1736666 := by exact prefixLift 1736666
  have htrace : WordTrace (prefixWord ++ tailWord_1736666) baseStart_1736666 baseEnd_1736666 := by
    simpa [prefixWord, tailWord_1736666, baseEnd_1736666] using wordTrace_append hprefix tailTrace_1736666
  have hstable : (prefixWord ++ tailWord_1736666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736666).length < 2 ^ (prefixWord ++ tailWord_1736666).sum := by decide
  have hdescent : baseEnd_1736666 < baseStart_1736666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736709 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_1736709 : Nat := 118140960795 + 1736709 * 2 ^ 59
def prefixEnd_1736709 : Nat := 4983230072969 + 3 ^ 40 * 1736709 * 2
def baseEnd_1736709 : Nat := 594510982659567234500351

theorem tailTrace_1736709 : CollatzResearch.WordTrace tailWord_1736709 prefixEnd_1736709 594510982659567234500351 := by
  unfold tailWord_1736709
  simp only [CollatzResearch.WordTrace]
  refine ⟨63342981065207374128277181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42228654043471582752184787 63342981065207374128277181)
  ·
    refine ⟨23753617899452765298103943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63342981065207374128277181 23753617899452765298103943)
    ·
      refine ⟨35630426849179147947155915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23753617899452765298103943 35630426849179147947155915)
      ·
        refine ⟨53445640273768721920733873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35630426849179147947155915 53445640273768721920733873)
        ·
          refine ⟨40084230205326541440550405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53445640273768721920733873 40084230205326541440550405)
          ·
            refine ⟨7515793163498726520103201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40084230205326541440550405 7515793163498726520103201)
            ·
              refine ⟨5636844872624044890077401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7515793163498726520103201 5636844872624044890077401)
              ·
                refine ⟨4227633654468033667558051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636844872624044890077401 4227633654468033667558051)
                ·
                  refine ⟨6341450481702050501337077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227633654468033667558051 6341450481702050501337077)
                  ·
                    refine ⟨594510982659567234500351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6341450481702050501337077 594510982659567234500351)
                    ·
                      rfl

theorem cell22_1736709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_1736709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736709 prefixEnd_1736709 := by exact prefixLift 1736709
  have htrace : WordTrace (prefixWord ++ tailWord_1736709) baseStart_1736709 baseEnd_1736709 := by
    simpa [prefixWord, tailWord_1736709, baseEnd_1736709] using wordTrace_append hprefix tailTrace_1736709
  have hstable : (prefixWord ++ tailWord_1736709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736709).length < 2 ^ (prefixWord ++ tailWord_1736709).sum := by decide
  have hdescent : baseEnd_1736709 < baseStart_1736709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736711 : List Nat := [1, 1, 4, 3, 1, 2, 1, 5, 4]
def baseStart_1736711 : Nat := 118140960795 + 1736711 * 2 ^ 59
def prefixEnd_1736711 : Nat := 4983230072969 + 3 ^ 40 * 1736711 * 2
def baseEnd_1736711 : Nat := 198170555766813298650115

theorem tailTrace_1736711 : CollatzResearch.WordTrace tailWord_1736711 prefixEnd_1736711 198170555766813298650115 := by
  unfold tailWord_1736711
  simp only [CollatzResearch.WordTrace]
  refine ⟨63343054011200128469849987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42228702674133418979899991 63343054011200128469849987)
  ·
    refine ⟨95014581016800192704774981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63343054011200128469849987 95014581016800192704774981)
    ·
      refine ⟨17815233940650036132145309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95014581016800192704774981 17815233940650036132145309)
      ·
        refine ⟨6680712727743763549554491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17815233940650036132145309 6680712727743763549554491)
        ·
          refine ⟨10021069091615645324331737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680712727743763549554491 10021069091615645324331737)
          ·
            refine ⟨7515801818711733993248803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10021069091615645324331737 7515801818711733993248803)
            ·
              refine ⟨11273702728067600989873205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7515801818711733993248803 11273702728067600989873205)
              ·
                refine ⟨1056909630756337592800613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11273702728067600989873205 1056909630756337592800613)
                ·
                  refine ⟨198170555766813298650115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056909630756337592800613 198170555766813298650115)
                  ·
                    rfl

theorem cell22_1736711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 4].length) (baseStart_1736711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736711 prefixEnd_1736711 := by exact prefixLift 1736711
  have htrace : WordTrace (prefixWord ++ tailWord_1736711) baseStart_1736711 baseEnd_1736711 := by
    simpa [prefixWord, tailWord_1736711, baseEnd_1736711] using wordTrace_append hprefix tailTrace_1736711
  have hstable : (prefixWord ++ tailWord_1736711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736711).length < 2 ^ (prefixWord ++ tailWord_1736711).sum := by decide
  have hdescent : baseEnd_1736711 < baseStart_1736711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736717 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1736717 : Nat := 118140960795 + 1736717 * 2 ^ 59
def prefixEnd_1736717 : Nat := 4983230072969 + 3 ^ 40 * 1736717 * 2
def baseEnd_1736717 : Nat := 198171240407685960100109

theorem tailTrace_1736717 : CollatzResearch.WordTrace tailWord_1736717 prefixEnd_1736717 198171240407685960100109 := by
  unfold tailWord_1736717
  simp only [CollatzResearch.WordTrace]
  refine ⟨63343272849178391494568405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42228848566118927663045603 63343272849178391494568405)
  ·
    refine ⟨1484607957402618550653947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 63343272849178391494568405 1484607957402618550653947)
    ·
      refine ⟨2226911936103927825980921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1484607957402618550653947 2226911936103927825980921)
      ·
        refine ⟨1670183952077945869485691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2226911936103927825980921 1670183952077945869485691)
        ·
          refine ⟨2505275928116918804228537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670183952077945869485691 2505275928116918804228537)
          ·
            refine ⟨1878956946087689103171403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505275928116918804228537 1878956946087689103171403)
            ·
              refine ⟨2818435419131533654757105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878956946087689103171403 2818435419131533654757105)
              ·
                refine ⟨2113826564348650241067829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2818435419131533654757105 2113826564348650241067829)
                ·
                  refine ⟨198171240407685960100109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2113826564348650241067829 198171240407685960100109)
                  ·
                    rfl

theorem cell22_1736717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1736717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736717 prefixEnd_1736717 := by exact prefixLift 1736717
  have htrace : WordTrace (prefixWord ++ tailWord_1736717) baseStart_1736717 baseEnd_1736717 := by
    simpa [prefixWord, tailWord_1736717, baseEnd_1736717] using wordTrace_append hprefix tailTrace_1736717
  have hstable : (prefixWord ++ tailWord_1736717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736717).length < 2 ^ (prefixWord ++ tailWord_1736717).sum := by decide
  have hdescent : baseEnd_1736717 < baseStart_1736717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736861 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1736861 : Nat := 118140960795 + 1736861 * 2 ^ 59
def prefixEnd_1736861 : Nat := 4983230072969 + 3 ^ 40 * 1736861 * 2
def baseEnd_1736861 : Nat := 594563015365889504699885

theorem tailTrace_1736861 : CollatzResearch.WordTrace tailWord_1736861 prefixEnd_1736861 594563015365889504699885 := by
  unfold tailWord_1736861
  simp only [CollatzResearch.WordTrace]
  refine ⟨63348524960656704087810437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42232349973771136058540291 63348524960656704087810437)
  ·
    refine ⟨11877848430123132016464457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63348524960656704087810437 11877848430123132016464457)
    ·
      refine ⟨8908386322592349012348343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11877848430123132016464457 8908386322592349012348343)
      ·
        refine ⟨13362579483888523518522515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8908386322592349012348343 13362579483888523518522515)
        ·
          refine ⟨20043869225832785277783773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13362579483888523518522515 20043869225832785277783773)
          ·
            refine ⟨7516450959687294479168915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20043869225832785277783773 7516450959687294479168915)
            ·
              refine ⟨11274676439530941718753373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7516450959687294479168915 11274676439530941718753373)
              ·
                refine ⟨4228003664824103144532515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11274676439530941718753373 4228003664824103144532515)
                ·
                  refine ⟨6342005497236154716798773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228003664824103144532515 6342005497236154716798773)
                  ·
                    refine ⟨594563015365889504699885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6342005497236154716798773 594563015365889504699885)
                    ·
                      rfl

theorem cell22_1736861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1736861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736861 prefixEnd_1736861 := by exact prefixLift 1736861
  have htrace : WordTrace (prefixWord ++ tailWord_1736861) baseStart_1736861 baseEnd_1736861 := by
    simpa [prefixWord, tailWord_1736861, baseEnd_1736861] using wordTrace_append hprefix tailTrace_1736861
  have hstable : (prefixWord ++ tailWord_1736861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736861).length < 2 ^ (prefixWord ++ tailWord_1736861).sum := by decide
  have hdescent : baseEnd_1736861 < baseStart_1736861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736925 : List Nat := [1, 4, 3, 2, 1, 3, 2, 6]
def baseStart_1736925 : Nat := 118140960795 + 1736925 * 2 ^ 59
def prefixEnd_1736925 : Nat := 4983230072969 + 3 ^ 40 * 1736925 * 2
def baseEnd_1736925 : Nat := 66064991541534963455521

theorem tailTrace_1736925 : CollatzResearch.WordTrace tailWord_1736925 prefixEnd_1736925 66064991541534963455521 := by
  unfold tailWord_1736925
  simp only [CollatzResearch.WordTrace]
  refine ⟨63350859232424843018140229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42233906154949895345426819 63350859232424843018140229)
  ·
    refine ⟨11878286106079658065901293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63350859232424843018140229 11878286106079658065901293)
    ·
      refine ⟨4454357289779871774712985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11878286106079658065901293 4454357289779871774712985)
      ·
        refine ⟨3340767967334903831034739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4454357289779871774712985 3340767967334903831034739)
        ·
          refine ⟨5011151951002355746552109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340767967334903831034739 5011151951002355746552109)
          ·
            refine ⟨1879181981625883404957041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5011151951002355746552109 1879181981625883404957041)
            ·
              refine ⟨1409386486219412553717781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879181981625883404957041 1409386486219412553717781)
              ·
                refine ⟨66064991541534963455521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1409386486219412553717781 66064991541534963455521)
                ·
                  rfl

theorem cell22_1736925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 6].length) (baseStart_1736925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736925 prefixEnd_1736925 := by exact prefixLift 1736925
  have htrace : WordTrace (prefixWord ++ tailWord_1736925) baseStart_1736925 baseEnd_1736925 := by
    simpa [prefixWord, tailWord_1736925, baseEnd_1736925] using wordTrace_append hprefix tailTrace_1736925
  have hstable : (prefixWord ++ tailWord_1736925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736925).length < 2 ^ (prefixWord ++ tailWord_1736925).sum := by decide
  have hdescent : baseEnd_1736925 < baseStart_1736925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736936 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 7]
def baseStart_1736936 : Nat := 118140960795 + 1736936 * 2 ^ 59
def prefixEnd_1736936 : Nat := 4983230072969 + 3 ^ 40 * 1736936 * 2
def baseEnd_1736936 : Nat := 198196229799538103024885

theorem tailTrace_1736936 : CollatzResearch.WordTrace tailWord_1736936 prefixEnd_1736936 198196229799538103024885 := by
  unfold tailWord_1736936
  simp only [CollatzResearch.WordTrace]
  refine ⟨31675630217692495948395331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42234173623589994597860441 31675630217692495948395331)
  ·
    refine ⟨47513445326538743922592997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31675630217692495948395331 47513445326538743922592997)
    ·
      refine ⟨8908770998726014485486187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47513445326538743922592997 8908770998726014485486187)
      ·
        refine ⟨13363156498089021728229281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8908770998726014485486187 13363156498089021728229281)
        ·
          refine ⟨10022367373566766296171961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13363156498089021728229281 10022367373566766296171961)
          ·
            refine ⟨7516775530175074722128971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10022367373566766296171961 7516775530175074722128971)
            ·
              refine ⟨11275163295262612083193457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7516775530175074722128971 11275163295262612083193457)
              ·
                refine ⟨8456372471446959062395093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11275163295262612083193457 8456372471446959062395093)
                ·
                  refine ⟨198196229799538103024885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8456372471446959062395093 198196229799538103024885)
                  ·
                    rfl

theorem cell22_1736936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_1736936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736936 prefixEnd_1736936 := by exact prefixLift 1736936
  have htrace : WordTrace (prefixWord ++ tailWord_1736936) baseStart_1736936 baseEnd_1736936 := by
    simpa [prefixWord, tailWord_1736936, baseEnd_1736936] using wordTrace_append hprefix tailTrace_1736936
  have hstable : (prefixWord ++ tailWord_1736936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736936).length < 2 ^ (prefixWord ++ tailWord_1736936).sum := by decide
  have hdescent : baseEnd_1736936 < baseStart_1736936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736981 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 6]
def baseStart_1736981 : Nat := 118140960795 + 1736981 * 2 ^ 59
def prefixEnd_1736981 : Nat := 4983230072969 + 3 ^ 40 * 1736981 * 2
def baseEnd_1736981 : Nat := 198201364606083063899839

theorem tailTrace_1736981 : CollatzResearch.WordTrace tailWord_1736981 prefixEnd_1736981 198201364606083063899839 := by
  unfold tailWord_1736981
  simp only [CollatzResearch.WordTrace]
  refine ⟨63352901720221964582178797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42235267813481309721452531 63352901720221964582178797)
  ·
    refine ⟨23757338145083236718317049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63352901720221964582178797 23757338145083236718317049)
    ·
      refine ⟨17818003608812427538737787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23757338145083236718317049 17818003608812427538737787)
      ·
        refine ⟨26727005413218641308106681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17818003608812427538737787 26727005413218641308106681)
        ·
          refine ⟨20045254059913980981080011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26727005413218641308106681 20045254059913980981080011)
          ·
            refine ⟨30067881089870971471620017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20045254059913980981080011 30067881089870971471620017)
            ·
              refine ⟨22550910817403228603715013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30067881089870971471620017 22550910817403228603715013)
              ·
                refine ⟨4228295778263105363196565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22550910817403228603715013 4228295778263105363196565)
                ·
                  refine ⟨198201364606083063899839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4228295778263105363196565 198201364606083063899839)
                  ·
                    rfl

theorem cell22_1736981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_1736981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736981 prefixEnd_1736981 := by exact prefixLift 1736981
  have htrace : WordTrace (prefixWord ++ tailWord_1736981) baseStart_1736981 baseEnd_1736981 := by
    simpa [prefixWord, tailWord_1736981, baseEnd_1736981] using wordTrace_append hprefix tailTrace_1736981
  have hstable : (prefixWord ++ tailWord_1736981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736981).length < 2 ^ (prefixWord ++ tailWord_1736981).sum := by decide
  have hdescent : baseEnd_1736981 < baseStart_1736981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736983 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1736983 : Nat := 118140960795 + 1736983 * 2 ^ 59
def prefixEnd_1736983 : Nat := 4983230072969 + 3 ^ 40 * 1736983 * 2
def baseEnd_1736983 : Nat := 594604778459121853149511

theorem tailTrace_1736983 : CollatzResearch.WordTrace tailWord_1736983 prefixEnd_1736983 594604778459121853149511 := by
  unfold tailWord_1736983
  simp only [CollatzResearch.WordTrace]
  refine ⟨63352974666214718923751603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42235316444143145949167735 63352974666214718923751603)
  ·
    refine ⟨95029461999322078385627405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63352974666214718923751603 95029461999322078385627405)
    ·
      refine ⟨35636048249745779394610277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95029461999322078385627405 35636048249745779394610277)
      ·
        refine ⟨6681759046827333636489427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35636048249745779394610277 6681759046827333636489427)
        ·
          refine ⟨10022638570241000454734141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681759046827333636489427 10022638570241000454734141)
          ·
            refine ⟨3758489463840375170525303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10022638570241000454734141 3758489463840375170525303)
            ·
              refine ⟨5637734195760562755787955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758489463840375170525303 5637734195760562755787955)
              ·
                refine ⟨8456601293640844133681933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637734195760562755787955 8456601293640844133681933)
                ·
                  refine ⟨3171225485115316550130725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8456601293640844133681933 3171225485115316550130725)
                  ·
                    refine ⟨594604778459121853149511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171225485115316550130725 594604778459121853149511)
                    ·
                      rfl

theorem cell22_1736983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1736983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1736983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1736983 prefixEnd_1736983 := by exact prefixLift 1736983
  have htrace : WordTrace (prefixWord ++ tailWord_1736983) baseStart_1736983 baseEnd_1736983 := by
    simpa [prefixWord, tailWord_1736983, baseEnd_1736983] using wordTrace_append hprefix tailTrace_1736983
  have hstable : (prefixWord ++ tailWord_1736983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736983).length < 2 ^ (prefixWord ++ tailWord_1736983).sum := by decide
  have hdescent : baseEnd_1736983 < baseStart_1736983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737208 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_1737208 : Nat := 118140960795 + 1737208 * 2 ^ 59
def prefixEnd_1737208 : Nat := 4983230072969 + 3 ^ 40 * 1737208 * 2
def baseEnd_1737208 : Nat := 594681800557296266273821

theorem tailTrace_1737208 : CollatzResearch.WordTrace tailWord_1737208 prefixEnd_1737208 594681800557296266273821 := by
  unfold tailWord_1737208
  simp only [CollatzResearch.WordTrace]
  refine ⟨31680590545199791175346139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42240787393599721567128185 31680590545199791175346139)
  ·
    refine ⟨47520885817799686763019209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31680590545199791175346139 47520885817799686763019209)
    ·
      refine ⟨35640664363349765072264407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47520885817799686763019209 35640664363349765072264407)
      ·
        refine ⟨53460996545024647608396611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35640664363349765072264407 53460996545024647608396611)
        ·
          refine ⟨80191494817536971412594917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53460996545024647608396611 80191494817536971412594917)
          ·
            refine ⟨15035905278288182139861547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80191494817536971412594917 15035905278288182139861547)
            ·
              refine ⟨22553857917432273209792321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15035905278288182139861547 22553857917432273209792321)
              ·
                refine ⟨16915393438074204907344241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22553857917432273209792321 16915393438074204907344241)
                ·
                  refine ⟨12686545078555653680508181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16915393438074204907344241 12686545078555653680508181)
                  ·
                    refine ⟨594681800557296266273821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12686545078555653680508181 594681800557296266273821)
                    ·
                      rfl

theorem cell22_1737208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_1737208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737208 prefixEnd_1737208 := by exact prefixLift 1737208
  have htrace : WordTrace (prefixWord ++ tailWord_1737208) baseStart_1737208 baseEnd_1737208 := by
    simpa [prefixWord, tailWord_1737208, baseEnd_1737208] using wordTrace_append hprefix tailTrace_1737208
  have hstable : (prefixWord ++ tailWord_1737208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737208).length < 2 ^ (prefixWord ++ tailWord_1737208).sum := by decide
  have hdescent : baseEnd_1737208 < baseStart_1737208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737240 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 7]
def baseStart_1737240 : Nat := 118140960795 + 1737240 * 2 ^ 59
def prefixEnd_1737240 : Nat := 4983230072969 + 3 ^ 40 * 1737240 * 2
def baseEnd_1737240 : Nat := 198230918270419616491241

theorem tailTrace_1737240 : CollatzResearch.WordTrace tailWord_1737240 prefixEnd_1737240 198230918270419616491241 := by
  unfold tailWord_1737240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681174113141825907928587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42241565484189101210571449 31681174113141825907928587)
  ·
    refine ⟨47521761169712738861892881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31681174113141825907928587 47521761169712738861892881)
    ·
      refine ⟨35641320877284554146419661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47521761169712738861892881 35641320877284554146419661)
      ·
        refine ⟨13365495328981707804907373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35641320877284554146419661 13365495328981707804907373)
        ·
          refine ⟨5012060748368140426840265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13365495328981707804907373 5012060748368140426840265)
          ·
            refine ⟨3759045561276105320130199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5012060748368140426840265 3759045561276105320130199)
            ·
              refine ⟨5638568341914157980195299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759045561276105320130199 5638568341914157980195299)
              ·
                refine ⟨8457852512871236970292949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5638568341914157980195299 8457852512871236970292949)
                ·
                  refine ⟨198230918270419616491241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8457852512871236970292949 198230918270419616491241)
                  ·
                    rfl

theorem cell22_1737240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_1737240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737240 prefixEnd_1737240 := by exact prefixLift 1737240
  have htrace : WordTrace (prefixWord ++ tailWord_1737240) baseStart_1737240 baseEnd_1737240 := by
    simpa [prefixWord, tailWord_1737240, baseEnd_1737240] using wordTrace_append hprefix tailTrace_1737240
  have hstable : (prefixWord ++ tailWord_1737240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737240).length < 2 ^ (prefixWord ++ tailWord_1737240).sum := by decide
  have hdescent : baseEnd_1737240 < baseStart_1737240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737244 : List Nat := [2, 2, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_1737244 : Nat := 118140960795 + 1737244 * 2 ^ 59
def prefixEnd_1737244 : Nat := 4983230072969 + 3 ^ 40 * 1737244 * 2
def baseEnd_1737244 : Nat := 594694124093004172373711

theorem tailTrace_1737244 : CollatzResearch.WordTrace tailWord_1737244 prefixEnd_1737244 594694124093004172373711 := by
  unfold tailWord_1737244
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681247059134580249501393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42241662745512773666001857 31681247059134580249501393)
  ·
    refine ⟨23760935294350935187126045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31681247059134580249501393 23760935294350935187126045)
    ·
      refine ⟨8910350735381600695172267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23760935294350935187126045 8910350735381600695172267)
      ·
        refine ⟨13365526103072401042758401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8910350735381600695172267 13365526103072401042758401)
        ·
          refine ⟨10024144577304300782068801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13365526103072401042758401 10024144577304300782068801)
          ·
            refine ⟨7518108432978225586551601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10024144577304300782068801 7518108432978225586551601)
            ·
              refine ⟨5638581324733669189913701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518108432978225586551601 5638581324733669189913701)
              ·
                refine ⟨1057233998387562973108819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5638581324733669189913701 1057233998387562973108819)
                ·
                  refine ⟨1585850997581344459663229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057233998387562973108819 1585850997581344459663229)
                  ·
                    refine ⟨594694124093004172373711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1585850997581344459663229 594694124093004172373711)
                    ·
                      rfl

theorem cell22_1737244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_1737244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737244 prefixEnd_1737244 := by exact prefixLift 1737244
  have htrace : WordTrace (prefixWord ++ tailWord_1737244) baseStart_1737244 baseEnd_1737244 := by
    simpa [prefixWord, tailWord_1737244, baseEnd_1737244] using wordTrace_append hprefix tailTrace_1737244
  have hstable : (prefixWord ++ tailWord_1737244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737244).length < 2 ^ (prefixWord ++ tailWord_1737244).sum := by decide
  have hdescent : baseEnd_1737244 < baseStart_1737244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
