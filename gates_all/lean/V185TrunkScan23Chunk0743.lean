import V185TrunkScan23Chunk0742

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4393447 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4393447 : Nat := 118140960795 + 4393447 * 2 ^ 59
def prefixEnd_4393447 : Nat := 4983230072969 + 3 ^ 40 * 4393447 * 2
def baseEnd_4393447 : Nat := 2255950041053977352107411

theorem tailTrace_4393447 : CollatzResearch.WordTrace tailWord_4393447 prefixEnd_4393447 2255950041053977352107411 := by
  unfold tailWord_4393447
  simp only [CollatzResearch.WordTrace]
  refine ⟨160242176514299334855010595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106828117676199556570007063 160242176514299334855010595)
  ·
    refine ⟨240363264771449002282515893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160242176514299334855010595 240363264771449002282515893)
    ·
      refine ⟨22534056072323343963985865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 240363264771449002282515893 22534056072323343963985865)
      ·
        refine ⟨16900542054242507972989399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22534056072323343963985865 16900542054242507972989399)
        ·
          refine ⟨25350813081363761959484099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16900542054242507972989399 25350813081363761959484099)
          ·
            refine ⟨38026219622045642939226149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25350813081363761959484099 38026219622045642939226149)
            ·
              refine ⟨7129916179133558051104903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38026219622045642939226149 7129916179133558051104903)
              ·
                refine ⟨10694874268700337076657355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129916179133558051104903 10694874268700337076657355)
                ·
                  refine ⟨16042311403050505614986033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10694874268700337076657355 16042311403050505614986033)
                  ·
                    refine ⟨12031733552287879211239525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16042311403050505614986033 12031733552287879211239525)
                    ·
                      refine ⟨2255950041053977352107411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12031733552287879211239525 2255950041053977352107411)
                      ·
                        rfl

theorem cell23_4393447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4393447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393447 prefixEnd_4393447 := by exact prefixLift 4393447
  have htrace : WordTrace (prefixWord ++ tailWord_4393447) baseStart_4393447 baseEnd_4393447 := by
    simpa [prefixWord, tailWord_4393447, baseEnd_4393447] using wordTrace_append hprefix tailTrace_4393447
  have hstable : (prefixWord ++ tailWord_4393447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393447).length < 2 ^ (prefixWord ++ tailWord_4393447).sum := by decide
  have hdescent : baseEnd_4393447 < baseStart_4393447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393478 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4393478 : Nat := 118140960795 + 4393478 * 2 ^ 59
def prefixEnd_4393478 : Nat := 4983230072969 + 3 ^ 40 * 4393478 * 2
def baseEnd_4393478 : Nat := 751988652984755576939923

theorem tailTrace_4393478 : CollatzResearch.WordTrace tailWord_4393478 prefixEnd_4393478 751988652984755576939923 := by
  unfold tailWord_4393478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007603349287094598418409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106828871451458018099592725 5007603349287094598418409)
  ·
    refine ⟨3755702511965320948813807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5007603349287094598418409 3755702511965320948813807)
    ·
      refine ⟨5633553767947981423220711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3755702511965320948813807 5633553767947981423220711)
      ·
        refine ⟨8450330651921972134831067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5633553767947981423220711 8450330651921972134831067)
        ·
          refine ⟨12675495977882958202246601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8450330651921972134831067 12675495977882958202246601)
          ·
            refine ⟨9506621983412218651684951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12675495977882958202246601 9506621983412218651684951)
            ·
              refine ⟨14259932975118327977527427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9506621983412218651684951 14259932975118327977527427)
              ·
                refine ⟨21389899462677491966291141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14259932975118327977527427 21389899462677491966291141)
                ·
                  refine ⟨4010606149252029743679589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21389899462677491966291141 4010606149252029743679589)
                  ·
                    refine ⟨751988652984755576939923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4010606149252029743679589 751988652984755576939923)
                    ·
                      rfl

theorem cell23_4393478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4393478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393478 prefixEnd_4393478 := by exact prefixLift 4393478
  have htrace : WordTrace (prefixWord ++ tailWord_4393478) baseStart_4393478 baseEnd_4393478 := by
    simpa [prefixWord, tailWord_4393478, baseEnd_4393478] using wordTrace_append hprefix tailTrace_4393478
  have hstable : (prefixWord ++ tailWord_4393478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393478).length < 2 ^ (prefixWord ++ tailWord_4393478).sum := by decide
  have hdescent : baseEnd_4393478 < baseStart_4393478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393484 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_4393484 : Nat := 118140960795 + 4393484 * 2 ^ 59
def prefixEnd_4393484 : Nat := 4983230072969 + 3 ^ 40 * 4393484 * 2
def baseEnd_4393484 : Nat := 2255969039838193707344741

theorem tailTrace_4393484 : CollatzResearch.WordTrace tailWord_4393484 prefixEnd_4393484 2255969039838193707344741 := by
  unfold tailWord_4393484
  simp only [CollatzResearch.WordTrace]
  refine ⟨80121763007582645087053753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106829017343443526782738337 80121763007582645087053753)
  ·
    refine ⟨60091322255686983815290315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80121763007582645087053753 60091322255686983815290315)
    ·
      refine ⟨90136983383530475722935473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60091322255686983815290315 90136983383530475722935473)
      ·
        refine ⟨67602737537647856792201605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90136983383530475722935473 67602737537647856792201605)
        ·
          refine ⟨12675513288308973148537801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67602737537647856792201605 12675513288308973148537801)
          ·
            refine ⟨9506634966231729861403351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12675513288308973148537801 9506634966231729861403351)
            ·
              refine ⟨14259952449347594792105027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9506634966231729861403351 14259952449347594792105027)
              ·
                refine ⟨21389928674021392188157541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14259952449347594792105027 21389928674021392188157541)
                ·
                  refine ⟨4010611626379011035279539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21389928674021392188157541 4010611626379011035279539)
                  ·
                    refine ⟨6015917439568516552919309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4010611626379011035279539 6015917439568516552919309)
                    ·
                      refine ⟨2255969039838193707344741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6015917439568516552919309 2255969039838193707344741)
                      ·
                        rfl

theorem cell23_4393484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_4393484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393484 prefixEnd_4393484 := by exact prefixLift 4393484
  have htrace : WordTrace (prefixWord ++ tailWord_4393484) baseStart_4393484 baseEnd_4393484 := by
    simpa [prefixWord, tailWord_4393484, baseEnd_4393484] using wordTrace_append hprefix tailTrace_4393484
  have hstable : (prefixWord ++ tailWord_4393484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393484).length < 2 ^ (prefixWord ++ tailWord_4393484).sum := by decide
  have hdescent : baseEnd_4393484 < baseStart_4393484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393485 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4393485 : Nat := 118140960795 + 4393485 * 2 ^ 59
def prefixEnd_4393485 : Nat := 4983230072969 + 3 ^ 40 * 4393485 * 2
def baseEnd_4393485 : Nat := 2255969553318848203432237

theorem tailTrace_4393485 : CollatzResearch.WordTrace tailWord_4393485 prefixEnd_4393485 2255969553318848203432237 := by
  unfold tailWord_4393485
  simp only [CollatzResearch.WordTrace]
  refine ⟨160243562488161667344893909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106829041658774444896595939 160243562488161667344893909)
  ·
    refine ⟨3755708495816289078395951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 160243562488161667344893909 3755708495816289078395951)
    ·
      refine ⟨5633562743724433617593927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3755708495816289078395951 5633562743724433617593927)
      ·
        refine ⟨8450344115586650426390891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5633562743724433617593927 8450344115586650426390891)
        ·
          refine ⟨12675516173379975639586337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8450344115586650426390891 12675516173379975639586337)
          ·
            refine ⟨9506637130034981729689753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12675516173379975639586337 9506637130034981729689753)
            ·
              refine ⟨7129977847526236297267315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9506637130034981729689753 7129977847526236297267315)
              ·
                refine ⟨10694966771289354445900973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129977847526236297267315 10694966771289354445900973)
                ·
                  refine ⟨4010612539233507917212865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10694966771289354445900973 4010612539233507917212865)
                  ·
                    refine ⟨3007959404425130937909649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4010612539233507917212865 3007959404425130937909649)
                    ·
                      refine ⟨2255969553318848203432237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007959404425130937909649 2255969553318848203432237)
                      ·
                        rfl

theorem cell23_4393485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4393485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393485 prefixEnd_4393485 := by exact prefixLift 4393485
  have htrace : WordTrace (prefixWord ++ tailWord_4393485) baseStart_4393485 baseEnd_4393485 := by
    simpa [prefixWord, tailWord_4393485, baseEnd_4393485] using wordTrace_append hprefix tailTrace_4393485
  have hstable : (prefixWord ++ tailWord_4393485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393485).length < 2 ^ (prefixWord ++ tailWord_4393485).sum := by decide
  have hdescent : baseEnd_4393485 < baseStart_4393485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393520 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_4393520 : Nat := 118140960795 + 4393520 * 2 ^ 59
def prefixEnd_4393520 : Nat := 4983230072969 + 3 ^ 40 * 4393520 * 2
def baseEnd_4393520 : Nat := 2255987525141755566494575

theorem tailTrace_4393520 : CollatzResearch.WordTrace tailWord_4393520 prefixEnd_4393520 2255987525141755566494575 := by
  unfold tailWord_4393520
  simp only [CollatzResearch.WordTrace]
  refine ⟨80122419521517434161209007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106829892695356578881612009 80122419521517434161209007)
  ·
    refine ⟨120183629282276151241813511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80122419521517434161209007 120183629282276151241813511)
    ·
      refine ⟨180275443923414226862720267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120183629282276151241813511 180275443923414226862720267)
      ·
        refine ⟨270413165885121340294080401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180275443923414226862720267 270413165885121340294080401)
        ·
          refine ⟨202809874413841005220560301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270413165885121340294080401 202809874413841005220560301)
          ·
            refine ⟨76053702905190376957710113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202809874413841005220560301 76053702905190376957710113)
            ·
              refine ⟨57040277178892782718282585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76053702905190376957710113 57040277178892782718282585)
              ·
                refine ⟨42780207884169587038711939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57040277178892782718282585 42780207884169587038711939)
                ·
                  refine ⟨64170311826254380558067909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42780207884169587038711939 64170311826254380558067909)
                  ·
                    refine ⟨12031933467422696354637733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64170311826254380558067909 12031933467422696354637733)
                    ·
                      refine ⟨2255987525141755566494575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12031933467422696354637733 2255987525141755566494575)
                      ·
                        rfl

theorem cell23_4393520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_4393520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393520 prefixEnd_4393520 := by exact prefixLift 4393520
  have htrace : WordTrace (prefixWord ++ tailWord_4393520) baseStart_4393520 baseEnd_4393520 := by
    simpa [prefixWord, tailWord_4393520, baseEnd_4393520] using wordTrace_append hprefix tailTrace_4393520
  have hstable : (prefixWord ++ tailWord_4393520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393520).length < 2 ^ (prefixWord ++ tailWord_4393520).sum := by decide
  have hdescent : baseEnd_4393520 < baseStart_4393520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393547 : List Nat := [1, 1, 1, 1, 3, 1, 4, 6, 5]
def baseStart_4393547 : Nat := 118140960795 + 4393547 * 2 ^ 59
def prefixEnd_4393547 : Nat := 4983230072969 + 3 ^ 40 * 4393547 * 2
def baseEnd_4393547 : Nat := 250666821013269662317439

theorem tailTrace_4393547 : CollatzResearch.WordTrace tailWord_4393547 prefixEnd_4393547 250666821013269662317439 := by
  unfold tailWord_4393547
  simp only [CollatzResearch.WordTrace]
  refine ⟨160245823813937051933650895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106830549209291367955767263 160245823813937051933650895)
  ·
    refine ⟨240368735720905577900476343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160245823813937051933650895 240368735720905577900476343)
    ·
      refine ⟨360553103581358366850714515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240368735720905577900476343 360553103581358366850714515)
      ·
        refine ⟨540829655372037550276071773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360553103581358366850714515 540829655372037550276071773)
        ·
          refine ⟨202811120764514081353526915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 540829655372037550276071773 202811120764514081353526915)
          ·
            refine ⟨304216681146771122030290373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202811120764514081353526915 304216681146771122030290373)
            ·
              refine ⟨57040627715019585380679445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304216681146771122030290373 57040627715019585380679445)
              ·
                refine ⟨2673779424141543064719349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57040627715019585380679445 2673779424141543064719349)
                ·
                  refine ⟨250666821013269662317439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2673779424141543064719349 250666821013269662317439)
                  ·
                    rfl

theorem cell23_4393547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 5].length) (baseStart_4393547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393547 prefixEnd_4393547 := by exact prefixLift 4393547
  have htrace : WordTrace (prefixWord ++ tailWord_4393547) baseStart_4393547 baseEnd_4393547 := by
    simpa [prefixWord, tailWord_4393547, baseEnd_4393547] using wordTrace_append hprefix tailTrace_4393547
  have hstable : (prefixWord ++ tailWord_4393547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393547).length < 2 ^ (prefixWord ++ tailWord_4393547).sum := by decide
  have hdescent : baseEnd_4393547 < baseStart_4393547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393557 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_4393557 : Nat := 118140960795 + 4393557 * 2 ^ 59
def prefixEnd_4393557 : Nat := 4983230072969 + 3 ^ 40 * 4393557 * 2
def baseEnd_4393557 : Nat := 2256006523925971921731905

theorem tailTrace_4393557 : CollatzResearch.WordTrace tailWord_4393557 prefixEnd_4393557 2256006523925971921731905 := by
  unfold tailWord_4393557
  simp only [CollatzResearch.WordTrace]
  refine ⟨160246188543900823641514925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106830792362600549094343283 160246188543900823641514925)
  ·
    refine ⟨60092320703962808865568097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160246188543900823641514925 60092320703962808865568097)
    ·
      refine ⟨45069240527972106649176073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60092320703962808865568097 45069240527972106649176073)
      ·
        refine ⟨33801930395979079986882055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45069240527972106649176073 33801930395979079986882055)
        ·
          refine ⟨50702895593968619980323083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33801930395979079986882055 50702895593968619980323083)
          ·
            refine ⟨76054343390952929970484625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50702895593968619980323083 76054343390952929970484625)
            ·
              refine ⟨57040757543214697477863469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76054343390952929970484625 57040757543214697477863469)
              ·
                refine ⟨21390284078705511554198801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57040757543214697477863469 21390284078705511554198801)
                ·
                  refine ⟨16042713059029133665649101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21390284078705511554198801 16042713059029133665649101)
                  ·
                    refine ⟨6016017397135925124618413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16042713059029133665649101 6016017397135925124618413)
                    ·
                      refine ⟨2256006523925971921731905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6016017397135925124618413 2256006523925971921731905)
                      ·
                        rfl

theorem cell23_4393557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_4393557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393557 prefixEnd_4393557 := by exact prefixLift 4393557
  have htrace : WordTrace (prefixWord ++ tailWord_4393557) baseStart_4393557 baseEnd_4393557 := by
    simpa [prefixWord, tailWord_4393557, baseEnd_4393557] using wordTrace_append hprefix tailTrace_4393557
  have hstable : (prefixWord ++ tailWord_4393557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393557).length < 2 ^ (prefixWord ++ tailWord_4393557).sum := by decide
  have hdescent : baseEnd_4393557 < baseStart_4393557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393560 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 3, 7]
def baseStart_4393560 : Nat := 118140960795 + 4393560 * 2 ^ 59
def prefixEnd_4393560 : Nat := 4983230072969 + 3 ^ 40 * 4393560 * 2
def baseEnd_4393560 : Nat := 752002688122645136664797

theorem tailTrace_4393560 : CollatzResearch.WordTrace tailWord_4393560 prefixEnd_4393560 752002688122645136664797 := by
  unfold tailWord_4393560
  simp only [CollatzResearch.WordTrace]
  refine ⟨80123148981444977576937067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106830865308593303435916089 80123148981444977576937067)
  ·
    refine ⟨120184723472167466365405601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80123148981444977576937067 120184723472167466365405601)
    ·
      refine ⟨90138542604125599774054201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120184723472167466365405601 90138542604125599774054201)
      ·
        refine ⟨67603906953094199830540651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90138542604125599774054201 67603906953094199830540651)
        ·
          refine ⟨101405860429641299745810977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67603906953094199830540651 101405860429641299745810977)
          ·
            refine ⟨76054395322230974809358233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101405860429641299745810977 76054395322230974809358233)
            ·
              refine ⟨57040796491673231107018675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76054395322230974809358233 57040796491673231107018675)
              ·
                refine ⟨85561194737509846660528013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57040796491673231107018675 85561194737509846660528013)
                ·
                  refine ⟨32085448026566192497698005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85561194737509846660528013 32085448026566192497698005)
                  ·
                    refine ⟨752002688122645136664797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32085448026566192497698005 752002688122645136664797)
                    ·
                      rfl

theorem cell23_4393560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_4393560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393560 prefixEnd_4393560 := by exact prefixLift 4393560
  have htrace : WordTrace (prefixWord ++ tailWord_4393560) baseStart_4393560 baseEnd_4393560 := by
    simpa [prefixWord, tailWord_4393560, baseEnd_4393560] using wordTrace_append hprefix tailTrace_4393560
  have hstable : (prefixWord ++ tailWord_4393560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393560).length < 2 ^ (prefixWord ++ tailWord_4393560).sum := by decide
  have hdescent : baseEnd_4393560 < baseStart_4393560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393624 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 3, 4]
def baseStart_4393624 : Nat := 118140960795 + 4393624 * 2 ^ 59
def prefixEnd_4393624 : Nat := 4983230072969 + 3 ^ 40 * 4393624 * 2
def baseEnd_4393624 : Nat := 752013642376607719864699

theorem tailTrace_4393624 : CollatzResearch.WordTrace tailWord_4393624 prefixEnd_4393624 752013642376607719864699 := by
  unfold tailWord_4393624
  simp only [CollatzResearch.WordTrace]
  refine ⟨80124316117329047042101963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106832421489772062722802617 80124316117329047042101963)
  ·
    refine ⟨120186474175993570563152945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80124316117329047042101963 120186474175993570563152945)
    ·
      refine ⟨90139855631995177922364709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120186474175993570563152945 90139855631995177922364709)
      ·
        refine ⟨16901222930999095860443383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90139855631995177922364709 16901222930999095860443383)
        ·
          refine ⟨25351834396498643790665075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16901222930999095860443383 25351834396498643790665075)
          ·
            refine ⟨38027751594747965685997613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25351834396498643790665075 38027751594747965685997613)
            ·
              refine ⟨14260406848030487132249105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38027751594747965685997613 14260406848030487132249105)
              ·
                refine ⟨10695305136022865349186829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14260406848030487132249105 10695305136022865349186829)
                ·
                  refine ⟨4010739426008574505945061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10695305136022865349186829 4010739426008574505945061)
                  ·
                    refine ⟨752013642376607719864699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4010739426008574505945061 752013642376607719864699)
                    ·
                      rfl

theorem cell23_4393624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_4393624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393624 prefixEnd_4393624 := by exact prefixLift 4393624
  have htrace : WordTrace (prefixWord ++ tailWord_4393624) baseStart_4393624 baseEnd_4393624 := by
    simpa [prefixWord, tailWord_4393624, baseEnd_4393624] using wordTrace_append hprefix tailTrace_4393624
  have hstable : (prefixWord ++ tailWord_4393624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393624).length < 2 ^ (prefixWord ++ tailWord_4393624).sum := by decide
  have hdescent : baseEnd_4393624 < baseStart_4393624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393724 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_4393724 : Nat := 118140960795 + 4393724 * 2 ^ 59
def prefixEnd_4393724 : Nat := 4983230072969 + 3 ^ 40 * 4393724 * 2
def baseEnd_4393724 : Nat := 2256092275195272768343637

theorem tailTrace_4393724 : CollatzResearch.WordTrace tailWord_4393724 prefixEnd_4393724 2256092275195272768343637 := by
  unfold tailWord_4393724
  simp only [CollatzResearch.WordTrace]
  refine ⟨80126139767147905581422113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106834853022863874108562817 80126139767147905581422113)
  ·
    refine ⟨60094604825360929186066585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80126139767147905581422113 60094604825360929186066585)
    ·
      refine ⟨45070953619020696889549939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60094604825360929186066585 45070953619020696889549939)
      ·
        refine ⟨67606430428531045334324909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45070953619020696889549939 67606430428531045334324909)
        ·
          refine ⟨25352411410699142000371841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67606430428531045334324909 25352411410699142000371841)
          ·
            refine ⟨19014308558024356500278881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25352411410699142000371841 19014308558024356500278881)
            ·
              refine ⟨14260731418518267375209161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19014308558024356500278881 14260731418518267375209161)
              ·
                refine ⟨10695548563888700531406871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14260731418518267375209161 10695548563888700531406871)
                ·
                  refine ⟨16043322845833050797110307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10695548563888700531406871 16043322845833050797110307)
                  ·
                    refine ⟨24064984268749576195665461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16043322845833050797110307 24064984268749576195665461)
                    ·
                      refine ⟨2256092275195272768343637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24064984268749576195665461 2256092275195272768343637)
                      ·
                        rfl

theorem cell23_4393724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_4393724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393724 prefixEnd_4393724 := by exact prefixLift 4393724
  have htrace : WordTrace (prefixWord ++ tailWord_4393724) baseStart_4393724 baseEnd_4393724 := by
    simpa [prefixWord, tailWord_4393724, baseEnd_4393724] using wordTrace_append hprefix tailTrace_4393724
  have hstable : (prefixWord ++ tailWord_4393724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393724).length < 2 ^ (prefixWord ++ tailWord_4393724).sum := by decide
  have hdescent : baseEnd_4393724 < baseStart_4393724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393751 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_4393751 : Nat := 118140960795 + 4393751 * 2 ^ 59
def prefixEnd_4393751 : Nat := 4983230072969 + 3 ^ 40 * 4393751 * 2
def baseEnd_4393751 : Nat := 2256106139172944162706013

theorem tailTrace_4393751 : CollatzResearch.WordTrace tailWord_4393751 prefixEnd_4393751 2256106139172944162706013 := by
  unfold tailWord_4393751
  simp only [CollatzResearch.WordTrace]
  refine ⟨160253264305197994774077107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106835509536798663182718071 160253264305197994774077107)
  ·
    refine ⟨240379896457796992161115661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160253264305197994774077107 240379896457796992161115661)
    ·
      refine ⟨90142461171673872060418373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240379896457796992161115661 90142461171673872060418373)
      ·
        refine ⟨16901711469688851011328445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90142461171673872060418373 16901711469688851011328445)
        ·
          refine ⟨6338141801133319129248167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16901711469688851011328445 6338141801133319129248167)
          ·
            refine ⟨9507212701699978693872251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338141801133319129248167 9507212701699978693872251)
            ·
              refine ⟨14260819052549968040808377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9507212701699978693872251 14260819052549968040808377)
              ·
                refine ⟨10695614289412476030606283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14260819052549968040808377 10695614289412476030606283)
                ·
                  refine ⟨16043421434118714045909425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10695614289412476030606283 16043421434118714045909425)
                  ·
                    refine ⟨12032566075589035534432069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16043421434118714045909425 12032566075589035534432069)
                    ·
                      refine ⟨2256106139172944162706013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12032566075589035534432069 2256106139172944162706013)
                      ·
                        rfl

theorem cell23_4393751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_4393751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393751 prefixEnd_4393751 := by exact prefixLift 4393751
  have htrace : WordTrace (prefixWord ++ tailWord_4393751) baseStart_4393751 baseEnd_4393751 := by
    simpa [prefixWord, tailWord_4393751, baseEnd_4393751] using wordTrace_append hprefix tailTrace_4393751
  have hstable : (prefixWord ++ tailWord_4393751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393751).length < 2 ^ (prefixWord ++ tailWord_4393751).sum := by decide
  have hdescent : baseEnd_4393751 < baseStart_4393751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393771 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 3]
def baseStart_4393771 : Nat := 118140960795 + 4393771 * 2 ^ 59
def prefixEnd_4393771 : Nat := 4983230072969 + 3 ^ 40 * 4393771 * 2
def baseEnd_4393771 : Nat := 2256116408786034084455921

theorem tailTrace_4393771 : CollatzResearch.WordTrace tailWord_4393771 prefixEnd_4393771 2256116408786034084455921 := by
  unfold tailWord_4393771
  simp only [CollatzResearch.WordTrace]
  refine ⟨160253993765125538189805167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106835995843417025459870111 160253993765125538189805167)
  ·
    refine ⟨240380990647688307284707751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160253993765125538189805167 240380990647688307284707751)
    ·
      refine ⟨360571485971532460927061627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240380990647688307284707751 360571485971532460927061627)
      ·
        refine ⟨540857228957298691390592441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360571485971532460927061627 540857228957298691390592441)
        ·
          refine ⟨405642921717974018542944331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540857228957298691390592441 405642921717974018542944331)
          ·
            refine ⟨608464382576961027814416497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405642921717974018542944331 608464382576961027814416497)
            ·
              refine ⟨456348286932720770860812373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608464382576961027814416497 456348286932720770860812373)
              ·
                refine ⟨5347831487492821533525145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 456348286932720770860812373 5347831487492821533525145)
                ·
                  refine ⟨4010873615619616150143859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5347831487492821533525145 4010873615619616150143859)
                  ·
                    refine ⟨6016310423429424225215789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4010873615619616150143859 6016310423429424225215789)
                    ·
                      refine ⟨2256116408786034084455921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6016310423429424225215789 2256116408786034084455921)
                      ·
                        rfl

theorem cell23_4393771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 3].length) (baseStart_4393771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393771 prefixEnd_4393771 := by exact prefixLift 4393771
  have htrace : WordTrace (prefixWord ++ tailWord_4393771) baseStart_4393771 baseEnd_4393771 := by
    simpa [prefixWord, tailWord_4393771, baseEnd_4393771] using wordTrace_append hprefix tailTrace_4393771
  have hstable : (prefixWord ++ tailWord_4393771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393771).length < 2 ^ (prefixWord ++ tailWord_4393771).sum := by decide
  have hdescent : baseEnd_4393771 < baseStart_4393771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393815 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 1, 3, 2]
def baseStart_4393815 : Nat := 118140960795 + 4393815 * 2 ^ 59
def prefixEnd_4393815 : Nat := 4983230072969 + 3 ^ 40 * 4393815 * 2
def baseEnd_4393815 : Nat := 2256139001934831912305719

theorem tailTrace_4393815 : CollatzResearch.WordTrace tailWord_4393815 prefixEnd_4393815 2256139001934831912305719 := by
  unfold tailWord_4393815
  simp only [CollatzResearch.WordTrace]
  refine ⟨160255598576966133704406899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106837065717977422469604599 160255598576966133704406899)
  ·
    refine ⟨240383397865449200556610349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160255598576966133704406899 240383397865449200556610349)
    ·
      refine ⟨90143774199543450208728881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240383397865449200556610349 90143774199543450208728881)
      ·
        refine ⟨67607830649657587656546661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90143774199543450208728881 67607830649657587656546661)
        ·
          refine ⟨12676468246810797685602499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67607830649657587656546661 12676468246810797685602499)
          ·
            refine ⟨19014702370216196528403749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12676468246810797685602499 19014702370216196528403749)
            ·
              refine ⟨3565256694415536849075703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19014702370216196528403749 3565256694415536849075703)
              ·
                refine ⟨5347885041623305273613555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565256694415536849075703 5347885041623305273613555)
                ·
                  refine ⟨8021827562434957910420333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5347885041623305273613555 8021827562434957910420333)
                  ·
                    refine ⟨3008185335913109216407625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8021827562434957910420333 3008185335913109216407625)
                    ·
                      refine ⟨2256139001934831912305719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008185335913109216407625 2256139001934831912305719)
                      ·
                        rfl

theorem cell23_4393815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_4393815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393815 prefixEnd_4393815 := by exact prefixLift 4393815
  have htrace : WordTrace (prefixWord ++ tailWord_4393815) baseStart_4393815 baseEnd_4393815 := by
    simpa [prefixWord, tailWord_4393815, baseEnd_4393815] using wordTrace_append hprefix tailTrace_4393815
  have hstable : (prefixWord ++ tailWord_4393815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393815).length < 2 ^ (prefixWord ++ tailWord_4393815).sum := by decide
  have hdescent : baseEnd_4393815 < baseStart_4393815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393824 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_4393824 : Nat := 118140960795 + 4393824 * 2 ^ 59
def prefixEnd_4393824 : Nat := 4983230072969 + 3 ^ 40 * 4393824 * 2
def baseEnd_4393824 : Nat := 2256143623260722377093177

theorem tailTrace_4393824 : CollatzResearch.WordTrace tailWord_4393824 prefixEnd_4393824 2256143623260722377093177 := by
  unfold tailWord_4393824
  simp only [CollatzResearch.WordTrace]
  refine ⟨80127963416966764120742263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106837284555955685494323017 80127963416966764120742263)
  ·
    refine ⟨120191945125450146181113395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80127963416966764120742263 120191945125450146181113395)
    ·
      refine ⟨180287917688175219271670093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120191945125450146181113395 180287917688175219271670093)
      ·
        refine ⟨67607969133065707226876285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180287917688175219271670093 67607969133065707226876285)
        ·
          refine ⟨25352988424899640210078607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67607969133065707226876285 25352988424899640210078607)
          ·
            refine ⟨38029482637349460315117911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25352988424899640210078607 38029482637349460315117911)
            ·
              refine ⟨57044223956024190472676867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38029482637349460315117911 57044223956024190472676867)
              ·
                refine ⟨85566335934036285709015301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57044223956024190472676867 85566335934036285709015301)
                ·
                  refine ⟨16043687987631803570440369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85566335934036285709015301 16043687987631803570440369)
                  ·
                    refine ⟨12032765990723852677830277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16043687987631803570440369 12032765990723852677830277)
                    ·
                      refine ⟨2256143623260722377093177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12032765990723852677830277 2256143623260722377093177)
                      ·
                        rfl

theorem cell23_4393824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_4393824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393824 prefixEnd_4393824 := by exact prefixLift 4393824
  have htrace : WordTrace (prefixWord ++ tailWord_4393824) baseStart_4393824 baseEnd_4393824 := by
    simpa [prefixWord, tailWord_4393824, baseEnd_4393824] using wordTrace_append hprefix tailTrace_4393824
  have hstable : (prefixWord ++ tailWord_4393824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393824).length < 2 ^ (prefixWord ++ tailWord_4393824).sum := by decide
  have hdescent : baseEnd_4393824 < baseStart_4393824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393845 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4393845 : Nat := 118140960795 + 4393845 * 2 ^ 59
def prefixEnd_4393845 : Nat := 4983230072969 + 3 ^ 40 * 4393845 * 2
def baseEnd_4393845 : Nat := 2256154406354466794930581

theorem tailTrace_4393845 : CollatzResearch.WordTrace tailWord_4393845 prefixEnd_4393845 2256154406354466794930581 := by
  unfold tailWord_4393845
  simp only [CollatzResearch.WordTrace]
  refine ⟨160256692766857448827998989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106837795177904965885332659 160256692766857448827998989)
  ·
    refine ⟨60096259787571543310499621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160256692766857448827998989 60096259787571543310499621)
    ·
      refine ⟨11268048710169664370718679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60096259787571543310499621 11268048710169664370718679)
      ·
        refine ⟨16902073065254496556078019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11268048710169664370718679 16902073065254496556078019)
        ·
          refine ⟨25353109597881744834117029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16902073065254496556078019 25353109597881744834117029)
          ·
            refine ⟨4753708049602827156396943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25353109597881744834117029 4753708049602827156396943)
            ·
              refine ⟨7130562074404240734595415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753708049602827156396943 7130562074404240734595415)
              ·
                refine ⟨10695843111606361101893123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7130562074404240734595415 10695843111606361101893123)
                ·
                  refine ⟨16043764667409541652839685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10695843111606361101893123 16043764667409541652839685)
                  ·
                    refine ⟨3008205875139289059907441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16043764667409541652839685 3008205875139289059907441)
                    ·
                      refine ⟨2256154406354466794930581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008205875139289059907441 2256154406354466794930581)
                      ·
                        rfl

theorem cell23_4393845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4393845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393845 prefixEnd_4393845 := by exact prefixLift 4393845
  have htrace : WordTrace (prefixWord ++ tailWord_4393845) baseStart_4393845 baseEnd_4393845 := by
    simpa [prefixWord, tailWord_4393845, baseEnd_4393845] using wordTrace_append hprefix tailTrace_4393845
  have hstable : (prefixWord ++ tailWord_4393845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393845).length < 2 ^ (prefixWord ++ tailWord_4393845).sum := by decide
  have hdescent : baseEnd_4393845 < baseStart_4393845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393911 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 3, 4]
def baseStart_4393911 : Nat := 118140960795 + 4393911 * 2 ^ 59
def prefixEnd_4393911 : Nat := 4983230072969 + 3 ^ 40 * 4393911 * 2
def baseEnd_4393911 : Nat := 752062765359221178901759

theorem tailTrace_4393911 : CollatzResearch.WordTrace tailWord_4393911 prefixEnd_4393911 752062765359221178901759 := by
  unfold tailWord_4393911
  simp only [CollatzResearch.WordTrace]
  refine ⟨160259099984618342099901587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106839399989745561399934391 160259099984618342099901587)
  ·
    refine ⟨240388649976927513149852381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160259099984618342099901587 240388649976927513149852381)
    ·
      refine ⟨90145743741347817431194643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240388649976927513149852381 90145743741347817431194643)
      ·
        refine ⟨135218615612021726146791965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90145743741347817431194643 135218615612021726146791965)
        ·
          refine ⟨50706980854508147305046987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135218615612021726146791965 50706980854508147305046987)
          ·
            refine ⟨76060471281762220957570481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50706980854508147305046987 76060471281762220957570481)
            ·
              refine ⟨57045353461321665718177861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76060471281762220957570481 57045353461321665718177861)
              ·
                refine ⟨10696003773997812322158349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57045353461321665718177861 10696003773997812322158349)
                ·
                  refine ⟨4011001415249179620809381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10696003773997812322158349 4011001415249179620809381)
                  ·
                    refine ⟨752062765359221178901759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4011001415249179620809381 752062765359221178901759)
                    ·
                      rfl

theorem cell23_4393911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_4393911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393911 prefixEnd_4393911 := by exact prefixLift 4393911
  have htrace : WordTrace (prefixWord ++ tailWord_4393911) baseStart_4393911 baseEnd_4393911 := by
    simpa [prefixWord, tailWord_4393911, baseEnd_4393911] using wordTrace_append hprefix tailTrace_4393911
  have hstable : (prefixWord ++ tailWord_4393911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393911).length < 2 ^ (prefixWord ++ tailWord_4393911).sum := by decide
  have hdescent : baseEnd_4393911 < baseStart_4393911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393918 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_4393918 : Nat := 118140960795 + 4393918 * 2 ^ 59
def prefixEnd_4393918 : Nat := 4983230072969 + 3 ^ 40 * 4393918 * 2
def baseEnd_4393918 : Nat := 2256191890442245009317745

theorem tailTrace_4393918 : CollatzResearch.WordTrace tailWord_4393918 prefixEnd_4393918 2256191890442245009317745 := by
  unfold tailWord_4393918
  simp only [CollatzResearch.WordTrace]
  refine ⟨20032419411949122786925801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106839570197061988196937605 20032419411949122786925801)
  ·
    refine ⟨15024314558961842090194351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20032419411949122786925801 15024314558961842090194351)
    ·
      refine ⟨22536471838442763135291527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15024314558961842090194351 22536471838442763135291527)
      ·
        refine ⟨33804707757664144702937291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22536471838442763135291527 33804707757664144702937291)
        ·
          refine ⟨50707061636496217054405937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33804707757664144702937291 50707061636496217054405937)
          ·
            refine ⟨38030296227372162790804453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50707061636496217054405937 38030296227372162790804453)
            ·
              refine ⟨7130680542632280523275835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38030296227372162790804453 7130680542632280523275835)
              ·
                refine ⟨10696020813948420784913753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7130680542632280523275835 10696020813948420784913753)
                ·
                  refine ⟨8022015610461315588685315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10696020813948420784913753 8022015610461315588685315)
                  ·
                    refine ⟨12033023415691973383027973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8022015610461315588685315 12033023415691973383027973)
                    ·
                      refine ⟨2256191890442245009317745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12033023415691973383027973 2256191890442245009317745)
                      ·
                        rfl

theorem cell23_4393918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_4393918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393918 prefixEnd_4393918 := by exact prefixLift 4393918
  have htrace : WordTrace (prefixWord ++ tailWord_4393918) baseStart_4393918 baseEnd_4393918 := by
    simpa [prefixWord, tailWord_4393918, baseEnd_4393918] using wordTrace_append hprefix tailTrace_4393918
  have hstable : (prefixWord ++ tailWord_4393918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393918).length < 2 ^ (prefixWord ++ tailWord_4393918).sum := by decide
  have hdescent : baseEnd_4393918 < baseStart_4393918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393945 : List Nat := [1, 2, 1, 2, 5, 2, 1, 4, 1, 4]
def baseStart_4393945 : Nat := 118140960795 + 4393945 * 2 ^ 59
def prefixEnd_4393945 : Nat := 4983230072969 + 3 ^ 40 * 4393945 * 2
def baseEnd_4393945 : Nat := 752068584806638801226707

theorem tailTrace_4393945 : CollatzResearch.WordTrace tailWord_4393945 prefixEnd_4393945 752068584806638801226707 := by
  unfold tailWord_4393945
  simp only [CollatzResearch.WordTrace]
  refine ⟨160260340066495165906639289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106840226710996777271092859 160260340066495165906639289)
  ·
    refine ⟨120195255049871374429979467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160260340066495165906639289 120195255049871374429979467)
    ·
      refine ⟨180292882574807061644969201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120195255049871374429979467 180292882574807061644969201)
      ·
        refine ⟨135219661931105296233726901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180292882574807061644969201 135219661931105296233726901)
        ·
          refine ⟨12676843306041121521911897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135219661931105296233726901 12676843306041121521911897)
          ·
            refine ⟨9507632479530841141433923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12676843306041121521911897 9507632479530841141433923)
            ·
              refine ⟨14261448719296261712150885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9507632479530841141433923 14261448719296261712150885)
              ·
                refine ⟨2674021634868049071028291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14261448719296261712150885 2674021634868049071028291)
                ·
                  refine ⟨4011032452302073606542437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674021634868049071028291 4011032452302073606542437)
                  ·
                    refine ⟨752068584806638801226707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4011032452302073606542437 752068584806638801226707)
                    ·
                      rfl

theorem cell23_4393945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 4].length) (baseStart_4393945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393945 prefixEnd_4393945 := by exact prefixLift 4393945
  have htrace : WordTrace (prefixWord ++ tailWord_4393945) baseStart_4393945 baseEnd_4393945 := by
    simpa [prefixWord, tailWord_4393945, baseEnd_4393945] using wordTrace_append hprefix tailTrace_4393945
  have hstable : (prefixWord ++ tailWord_4393945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393945).length < 2 ^ (prefixWord ++ tailWord_4393945).sum := by decide
  have hdescent : baseEnd_4393945 < baseStart_4393945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393984 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 10]
def baseStart_4393984 : Nat := 118140960795 + 4393984 * 2 ^ 59
def prefixEnd_4393984 : Nat := 4983230072969 + 3 ^ 40 * 4393984 * 2
def baseEnd_4393984 : Nat := 752075260055147250364147

theorem tailTrace_4393984 : CollatzResearch.WordTrace tailWord_4393984 prefixEnd_4393984 752075260055147250364147 := by
  unfold tailWord_4393984
  simp only [CollatzResearch.WordTrace]
  refine ⟨80130881256676937783654503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106841175008902583711539337 80130881256676937783654503)
  ·
    refine ⟨120196321885015406675481755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80130881256676937783654503 120196321885015406675481755)
    ·
      refine ⟨180294482827523110013222633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120196321885015406675481755 180294482827523110013222633)
      ·
        refine ⟨135220862120642332509916975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180294482827523110013222633 135220862120642332509916975)
        ·
          refine ⟨202831293180963498764875463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135220862120642332509916975 202831293180963498764875463)
          ·
            refine ⟨304246939771445248147313195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202831293180963498764875463 304246939771445248147313195)
            ·
              refine ⟨456370409657167872220969793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304246939771445248147313195 456370409657167872220969793)
              ·
                refine ⟨342277807242875904165727345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456370409657167872220969793 342277807242875904165727345)
                ·
                  refine ⟨256708355432156928124295509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342277807242875904165727345 256708355432156928124295509)
                  ·
                    refine ⟨752075260055147250364147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 256708355432156928124295509 752075260055147250364147)
                    ·
                      rfl

theorem cell23_4393984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_4393984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393984 prefixEnd_4393984 := by exact prefixLift 4393984
  have htrace : WordTrace (prefixWord ++ tailWord_4393984) baseStart_4393984 baseEnd_4393984 := by
    simpa [prefixWord, tailWord_4393984, baseEnd_4393984] using wordTrace_append hprefix tailTrace_4393984
  have hstable : (prefixWord ++ tailWord_4393984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393984).length < 2 ^ (prefixWord ++ tailWord_4393984).sum := by decide
  have hdescent : baseEnd_4393984 < baseStart_4393984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394018 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_4394018 : Nat := 118140960795 + 4394018 * 2 ^ 59
def prefixEnd_4394018 : Nat := 4983230072969 + 3 ^ 40 * 4394018 * 2
def baseEnd_4394018 : Nat := 752081079502564872689095

theorem tailTrace_4394018 : CollatzResearch.WordTrace tailWord_4394018 prefixEnd_4394018 752081079502564872689095 := by
  unfold tailWord_4394018
  simp only [CollatzResearch.WordTrace]
  refine ⟨40065750648807674843511677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106842001730153799582697805 40065750648807674843511677)
  ·
    refine ⟨15024656493302878066316879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40065750648807674843511677 15024656493302878066316879)
    ·
      refine ⟨22536984739954317099475319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15024656493302878066316879 22536984739954317099475319)
      ·
        refine ⟨33805477109931475649212979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22536984739954317099475319 33805477109931475649212979)
        ·
          refine ⟨50708215664897213473819469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33805477109931475649212979 50708215664897213473819469)
          ·
            refine ⟨19015580874336455052682301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50708215664897213473819469 19015580874336455052682301)
            ·
              refine ⟨7130842827876170644755863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19015580874336455052682301 7130842827876170644755863)
              ·
                refine ⟨10696264241814255967133795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7130842827876170644755863 10696264241814255967133795)
                ·
                  refine ⟨16044396362721383950700693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10696264241814255967133795 16044396362721383950700693)
                  ·
                    refine ⟨752081079502564872689095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16044396362721383950700693 752081079502564872689095)
                    ·
                      rfl

theorem cell23_4394018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_4394018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394018 prefixEnd_4394018 := by exact prefixLift 4394018
  have htrace : WordTrace (prefixWord ++ tailWord_4394018) baseStart_4394018 baseEnd_4394018 := by
    simpa [prefixWord, tailWord_4394018, baseEnd_4394018] using wordTrace_append hprefix tailTrace_4394018
  have hstable : (prefixWord ++ tailWord_4394018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394018).length < 2 ^ (prefixWord ++ tailWord_4394018).sum := by decide
  have hdescent : baseEnd_4394018 < baseStart_4394018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394021 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_4394021 : Nat := 118140960795 + 4394021 * 2 ^ 59
def prefixEnd_4394021 : Nat := 4983230072969 + 3 ^ 40 * 4394021 * 2
def baseEnd_4394021 : Nat := 2256244778949658106329771

theorem tailTrace_4394021 : CollatzResearch.WordTrace tailWord_4394021 prefixEnd_4394021 2256244778949658106329771 := by
  unfold tailWord_4394021
  simp only [CollatzResearch.WordTrace]
  refine ⟨160263112014219830886405917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106842074676146553924270611 160263112014219830886405917)
  ·
    refine ⟨60098667005332436582402219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160263112014219830886405917 60098667005332436582402219)
    ·
      refine ⟨90148000507998654873603329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60098667005332436582402219 90148000507998654873603329)
      ·
        refine ⟨67611000380998991155202497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90148000507998654873603329 67611000380998991155202497)
        ·
          refine ⟨50708250285749243366401873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67611000380998991155202497 50708250285749243366401873)
          ·
            refine ⟨38031187714311932524801405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50708250285749243366401873 38031187714311932524801405)
            ·
              refine ⟨14261695392866974696800527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38031187714311932524801405 14261695392866974696800527)
              ·
                refine ⟨21392543089300462045200791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14261695392866974696800527 21392543089300462045200791)
                ·
                  refine ⟨32088814633950693067801187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21392543089300462045200791 32088814633950693067801187)
                  ·
                    refine ⟨48133221950926039601701781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32088814633950693067801187 48133221950926039601701781)
                    ·
                      refine ⟨2256244778949658106329771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48133221950926039601701781 2256244778949658106329771)
                      ·
                        rfl

theorem cell23_4394021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_4394021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394021 prefixEnd_4394021 := by exact prefixLift 4394021
  have htrace : WordTrace (prefixWord ++ tailWord_4394021) baseStart_4394021 baseEnd_4394021 := by
    simpa [prefixWord, tailWord_4394021, baseEnd_4394021] using wordTrace_append hprefix tailTrace_4394021
  have hstable : (prefixWord ++ tailWord_4394021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394021).length < 2 ^ (prefixWord ++ tailWord_4394021).sum := by decide
  have hdescent : baseEnd_4394021 < baseStart_4394021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394036 : List Nat := [2, 5, 1, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_4394036 : Nat := 118140960795 + 4394036 * 2 ^ 59
def prefixEnd_4394036 : Nat := 4983230072969 + 3 ^ 40 * 4394036 * 2
def baseEnd_4394036 : Nat := 2256252481159475547642203

theorem tailTrace_4394036 : CollatzResearch.WordTrace tailWord_4394036 prefixEnd_4394036 2256252481159475547642203 := by
  unfold tailWord_4394036
  simp only [CollatzResearch.WordTrace]
  refine ⟨80131829554582744224100981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106842439406110325632134641 80131829554582744224100981)
  ·
    refine ⟨7512359020742132271009467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80131829554582744224100981 7512359020742132271009467)
    ·
      refine ⟨11268538531113198406514201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7512359020742132271009467 11268538531113198406514201)
      ·
        refine ⟨8451403898334898804885651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11268538531113198406514201 8451403898334898804885651)
        ·
          refine ⟨12677105847502348207328477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8451403898334898804885651 12677105847502348207328477)
          ·
            refine ⟨4753914692813380577748179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12677105847502348207328477 4753914692813380577748179)
            ·
              refine ⟨7130872039220070866622269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753914692813380577748179 7130872039220070866622269)
              ·
                refine ⟨2674077014707526574983351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7130872039220070866622269 2674077014707526574983351)
                ·
                  refine ⟨4011115522061289862475027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674077014707526574983351 4011115522061289862475027)
                  ·
                    refine ⟨6016673283091934793712541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4011115522061289862475027 6016673283091934793712541)
                    ·
                      refine ⟨2256252481159475547642203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6016673283091934793712541 2256252481159475547642203)
                      ·
                        rfl

theorem cell23_4394036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_4394036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394036 prefixEnd_4394036 := by exact prefixLift 4394036
  have htrace : WordTrace (prefixWord ++ tailWord_4394036) baseStart_4394036 baseEnd_4394036 := by
    simpa [prefixWord, tailWord_4394036, baseEnd_4394036] using wordTrace_append hprefix tailTrace_4394036
  have hstable : (prefixWord ++ tailWord_4394036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394036).length < 2 ^ (prefixWord ++ tailWord_4394036).sum := by decide
  have hdescent : baseEnd_4394036 < baseStart_4394036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394045 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_4394045 : Nat := 118140960795 + 4394045 * 2 ^ 59
def prefixEnd_4394045 : Nat := 4983230072969 + 3 ^ 40 * 4394045 * 2
def baseEnd_4394045 : Nat := 2256257102485366012429661

theorem tailTrace_4394045 : CollatzResearch.WordTrace tailWord_4394045 prefixEnd_4394045 2256257102485366012429661 := by
  unfold tailWord_4394045
  simp only [CollatzResearch.WordTrace]
  refine ⟨160263987366132882985279589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106842658244088588656853059 160263987366132882985279589)
  ·
    refine ⟨30049497631149915559739923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160263987366132882985279589 30049497631149915559739923)
    ·
      refine ⟨45074246446724873339609885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30049497631149915559739923 45074246446724873339609885)
      ·
        refine ⟨16902842417521827502353707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45074246446724873339609885 16902842417521827502353707)
        ·
          refine ⟨25354263626282741253530561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16902842417521827502353707 25354263626282741253530561)
          ·
            refine ⟨19015697719712055940147921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25354263626282741253530561 19015697719712055940147921)
            ·
              refine ⟨14261773289784041955110941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19015697719712055940147921 14261773289784041955110941)
              ·
                refine ⟨5348164983669015733166603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14261773289784041955110941 5348164983669015733166603)
                ·
                  refine ⟨8022247475503523599749905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5348164983669015733166603 8022247475503523599749905)
                  ·
                    refine ⟨6016685606627642699812429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8022247475503523599749905 6016685606627642699812429)
                    ·
                      refine ⟨2256257102485366012429661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6016685606627642699812429 2256257102485366012429661)
                      ·
                        rfl

theorem cell23_4394045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_4394045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394045 prefixEnd_4394045 := by exact prefixLift 4394045
  have htrace : WordTrace (prefixWord ++ tailWord_4394045) baseStart_4394045 baseEnd_4394045 := by
    simpa [prefixWord, tailWord_4394045, baseEnd_4394045] using wordTrace_append hprefix tailTrace_4394045
  have hstable : (prefixWord ++ tailWord_4394045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394045).length < 2 ^ (prefixWord ++ tailWord_4394045).sum := by decide
  have hdescent : baseEnd_4394045 < baseStart_4394045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394085 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 3, 3, 2]
def baseStart_4394085 : Nat := 118140960795 + 4394085 * 2 ^ 59
def prefixEnd_4394085 : Nat := 4983230072969 + 3 ^ 40 * 4394085 * 2
def baseEnd_4394085 : Nat := 2256277641711545855929477

theorem tailTrace_4394085 : CollatzResearch.WordTrace tailWord_4394085 prefixEnd_4394085 2256277641711545855929477 := by
  unfold tailWord_4394085
  simp only [CollatzResearch.WordTrace]
  refine ⟨160265446285987969816735709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106843630857325313211157139 160265446285987969816735709)
  ·
    refine ⟨60099542357245488681275891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160265446285987969816735709 60099542357245488681275891)
    ·
      refine ⟨90149313535868233021913837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60099542357245488681275891 90149313535868233021913837)
      ·
        refine ⟨33805992575950587383217689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90149313535868233021913837 33805992575950587383217689)
        ·
          refine ⟨25354494431962940537413267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33805992575950587383217689 25354494431962940537413267)
          ·
            refine ⟨38031741647944410806119901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25354494431962940537413267 38031741647944410806119901)
            ·
              refine ⟨14261903117979154052294963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38031741647944410806119901 14261903117979154052294963)
              ·
                refine ⟨21392854676968731078442445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14261903117979154052294963 21392854676968731078442445)
                ·
                  refine ⟨8022320503863274154415917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21392854676968731078442445 8022320503863274154415917)
                  ·
                    refine ⟨3008370188948727807905969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8022320503863274154415917 3008370188948727807905969)
                    ·
                      refine ⟨2256277641711545855929477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008370188948727807905969 2256277641711545855929477)
                      ·
                        rfl

theorem cell23_4394085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_4394085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394085 prefixEnd_4394085 := by exact prefixLift 4394085
  have htrace : WordTrace (prefixWord ++ tailWord_4394085) baseStart_4394085 baseEnd_4394085 := by
    simpa [prefixWord, tailWord_4394085, baseEnd_4394085] using wordTrace_append hprefix tailTrace_4394085
  have hstable : (prefixWord ++ tailWord_4394085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394085).length < 2 ^ (prefixWord ++ tailWord_4394085).sum := by decide
  have hdescent : baseEnd_4394085 < baseStart_4394085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394110 : List Nat := [4, 2, 4, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4394110 : Nat := 118140960795 + 4394110 * 2 ^ 59
def prefixEnd_4394110 : Nat := 4983230072969 + 3 ^ 40 * 4394110 * 2
def baseEnd_4394110 : Nat := 2256290478727908258116863

theorem tailTrace_4394110 : CollatzResearch.WordTrace tailWord_4394110 prefixEnd_4394110 2256290478727908258116863 := by
  unfold tailWord_4394110
  simp only [CollatzResearch.WordTrace]
  refine ⟨20033294763862174885799473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106844238740598266057597189 20033294763862174885799473)
  ·
    refine ⟨15024971072896631164349605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20033294763862174885799473 15024971072896631164349605)
    ·
      refine ⟨2817182076168118343315551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15024971072896631164349605 2817182076168118343315551)
      ·
        refine ⟨4225773114252177514973327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817182076168118343315551 4225773114252177514973327)
        ·
          refine ⟨6338659671378266272459991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225773114252177514973327 6338659671378266272459991)
          ·
            refine ⟨9507989507067399408689987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338659671378266272459991 9507989507067399408689987)
            ·
              refine ⟨14261984260601099113034981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9507989507067399408689987 14261984260601099113034981)
              ·
                refine ⟨2674122048862706083694059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14261984260601099113034981 2674122048862706083694059)
                ·
                  refine ⟨4011183073294059125541089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674122048862706083694059 4011183073294059125541089)
                  ·
                    refine ⟨3008387304970544344155817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4011183073294059125541089 3008387304970544344155817)
                    ·
                      refine ⟨2256290478727908258116863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008387304970544344155817 2256290478727908258116863)
                      ·
                        rfl

theorem cell23_4394110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4394110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394110 prefixEnd_4394110 := by exact prefixLift 4394110
  have htrace : WordTrace (prefixWord ++ tailWord_4394110) baseStart_4394110 baseEnd_4394110 := by
    simpa [prefixWord, tailWord_4394110, baseEnd_4394110] using wordTrace_append hprefix tailTrace_4394110
  have hstable : (prefixWord ++ tailWord_4394110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394110).length < 2 ^ (prefixWord ++ tailWord_4394110).sum := by decide
  have hdescent : baseEnd_4394110 < baseStart_4394110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394111 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_4394111 : Nat := 118140960795 + 4394111 * 2 ^ 59
def prefixEnd_4394111 : Nat := 4983230072969 + 3 ^ 40 * 4394111 * 2
def baseEnd_4394111 : Nat := 2256290992208562754204357

theorem tailTrace_4394111 : CollatzResearch.WordTrace tailWord_4394111 prefixEnd_4394111 2256290992208562754204357 := by
  unfold tailWord_4394111
  simp only [CollatzResearch.WordTrace]
  refine ⟨160266394583893776257182187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106844263055929184171454791 160266394583893776257182187)
  ·
    refine ⟨240399591875840664385773281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160266394583893776257182187 240399591875840664385773281)
    ·
      refine ⟨180299693906880498289329961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240399591875840664385773281 180299693906880498289329961)
      ·
        refine ⟨135224770430160373716997471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180299693906880498289329961 135224770430160373716997471)
        ·
          refine ⟨202837155645240560575496207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135224770430160373716997471 202837155645240560575496207)
          ·
            refine ⟨304255733467860840863244311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202837155645240560575496207 304255733467860840863244311)
            ·
              refine ⟨456383600201791261294866467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304255733467860840863244311 456383600201791261294866467)
              ·
                refine ⟨684575400302686891942299701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456383600201791261294866467 684575400302686891942299701)
                ·
                  refine ⟨64178943778376896119590597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 684575400302686891942299701 64178943778376896119590597)
                  ·
                    refine ⟨12033551958445668022423237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64178943778376896119590597 12033551958445668022423237)
                    ·
                      refine ⟨2256290992208562754204357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12033551958445668022423237 2256290992208562754204357)
                      ·
                        rfl

theorem cell23_4394111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_4394111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394111 prefixEnd_4394111 := by exact prefixLift 4394111
  have htrace : WordTrace (prefixWord ++ tailWord_4394111) baseStart_4394111 baseEnd_4394111 := by
    simpa [prefixWord, tailWord_4394111, baseEnd_4394111] using wordTrace_append hprefix tailTrace_4394111
  have hstable : (prefixWord ++ tailWord_4394111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394111).length < 2 ^ (prefixWord ++ tailWord_4394111).sum := by decide
  have hdescent : baseEnd_4394111 < baseStart_4394111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394138 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 9]
def baseStart_4394138 : Nat := 118140960795 + 4394138 * 2 ^ 59
def prefixEnd_4394138 : Nat := 4983230072969 + 3 ^ 40 * 4394138 * 2
def baseEnd_4394138 : Nat := 250700539576248238729637

theorem tailTrace_4394138 : CollatzResearch.WordTrace tailWord_4394138 prefixEnd_4394138 250700539576248238729637 := by
  unfold tailWord_4394138
  simp only [CollatzResearch.WordTrace]
  refine ⟨40066844838698989967103767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106844919569863973245610045 40066844838698989967103767)
  ·
    refine ⟨60100267258048484950655651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40066844838698989967103767 60100267258048484950655651)
    ·
      refine ⟨90150400887072727425983477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60100267258048484950655651 90150400887072727425983477)
      ·
        refine ⟨8451600083163068196185951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90150400887072727425983477 8451600083163068196185951)
        ·
          refine ⟨12677400124744602294278927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8451600083163068196185951 12677400124744602294278927)
          ·
            refine ⟨19016100187116903441418391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12677400124744602294278927 19016100187116903441418391)
            ·
              refine ⟨28524150280675355162127587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19016100187116903441418391 28524150280675355162127587)
              ·
                refine ⟨42786225421013032743191381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28524150280675355162127587 42786225421013032743191381)
                ·
                  refine ⟨250700539576248238729637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42786225421013032743191381 250700539576248238729637)
                  ·
                    rfl

theorem cell23_4394138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_4394138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394138 prefixEnd_4394138 := by exact prefixLift 4394138
  have htrace : WordTrace (prefixWord ++ tailWord_4394138) baseStart_4394138 baseEnd_4394138 := by
    simpa [prefixWord, tailWord_4394138, baseEnd_4394138] using wordTrace_append hprefix tailTrace_4394138
  have hstable : (prefixWord ++ tailWord_4394138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394138).length < 2 ^ (prefixWord ++ tailWord_4394138).sum := by decide
  have hdescent : baseEnd_4394138 < baseStart_4394138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394288 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 3, 6]
def baseStart_4394288 : Nat := 118140960795 + 4394288 * 2 ^ 59
def prefixEnd_4394288 : Nat := 4983230072969 + 3 ^ 40 * 4394288 * 2
def baseEnd_4394288 : Nat := 752127292761469520563681

theorem tailTrace_4394288 : CollatzResearch.WordTrace tailWord_4394288 prefixEnd_4394288 752127292761469520563681 := by
  unfold tailWord_4394288
  simp only [CollatzResearch.WordTrace]
  refine ⟨80136425152126267743187759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106848566869501690324250345 80136425152126267743187759)
  ·
    refine ⟨120204637728189401614781639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80136425152126267743187759 120204637728189401614781639)
    ·
      refine ⟨180306956592284102422172459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120204637728189401614781639 180306956592284102422172459)
      ·
        refine ⟨270460434888426153633258689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180306956592284102422172459 270460434888426153633258689)
        ·
          refine ⟨202845326166319615224944017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270460434888426153633258689 202845326166319615224944017)
          ·
            refine ⟨152133994624739711418708013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202845326166319615224944017 152133994624739711418708013)
            ·
              refine ⟨57050247984277391782015505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152133994624739711418708013 57050247984277391782015505)
              ·
                refine ⟨42787685988208043836511629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57050247984277391782015505 42787685988208043836511629)
                ·
                  refine ⟨16045382245578016438691861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42787685988208043836511629 16045382245578016438691861)
                  ·
                    refine ⟨752127292761469520563681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16045382245578016438691861 752127292761469520563681)
                    ·
                      rfl

theorem cell23_4394288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_4394288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394288 prefixEnd_4394288 := by exact prefixLift 4394288
  have htrace : WordTrace (prefixWord ++ tailWord_4394288) baseStart_4394288 baseEnd_4394288 := by
    simpa [prefixWord, tailWord_4394288, baseEnd_4394288] using wordTrace_append hprefix tailTrace_4394288
  have hstable : (prefixWord ++ tailWord_4394288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394288).length < 2 ^ (prefixWord ++ tailWord_4394288).sum := by decide
  have hdescent : baseEnd_4394288 < baseStart_4394288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394295 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 4, 6, 2]
def baseStart_4394295 : Nat := 118140960795 + 4394295 * 2 ^ 59
def prefixEnd_4394295 : Nat := 4983230072969 + 3 ^ 40 * 4394295 * 2
def baseEnd_4394295 : Nat := 2256385472648990034303511

theorem tailTrace_4394295 : CollatzResearch.WordTrace tailWord_4394295 prefixEnd_4394295 2256385472648990034303511 := by
  unfold tailWord_4394295
  simp only [CollatzResearch.WordTrace]
  refine ⟨160273105615227175681880339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106848737076818117121253559 160273105615227175681880339)
  ·
    refine ⟨240409658422840763522820509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160273105615227175681880339 240409658422840763522820509)
    ·
      refine ⟨90153621908565286321057691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240409658422840763522820509 90153621908565286321057691)
      ·
        refine ⟨135230432862847929481586537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90153621908565286321057691 135230432862847929481586537)
        ·
          refine ⟨101422824647135947111189903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135230432862847929481586537 101422824647135947111189903)
          ·
            refine ⟨152134236970703920666784855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101422824647135947111189903 152134236970703920666784855)
            ·
              refine ⟨228201355456055881000177283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152134236970703920666784855 228201355456055881000177283)
              ·
                refine ⟨342302033184083821500265925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228201355456055881000177283 342302033184083821500265925)
                ·
                  refine ⟨64181631222015716531299861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342302033184083821500265925 64181631222015716531299861)
                  ·
                    refine ⟨3008513963531986712404681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64181631222015716531299861 3008513963531986712404681)
                    ·
                      refine ⟨2256385472648990034303511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008513963531986712404681 2256385472648990034303511)
                      ·
                        rfl

theorem cell23_4394295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_4394295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394295 prefixEnd_4394295 := by exact prefixLift 4394295
  have htrace : WordTrace (prefixWord ++ tailWord_4394295) baseStart_4394295 baseEnd_4394295 := by
    simpa [prefixWord, tailWord_4394295, baseEnd_4394295] using wordTrace_append hprefix tailTrace_4394295
  have hstable : (prefixWord ++ tailWord_4394295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394295).length < 2 ^ (prefixWord ++ tailWord_4394295).sum := by decide
  have hdescent : baseEnd_4394295 < baseStart_4394295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394310 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4394310 : Nat := 118140960795 + 4394310 * 2 ^ 59
def prefixEnd_4394310 : Nat := 4983230072969 + 3 ^ 40 * 4394310 * 2
def baseEnd_4394310 : Nat := 2256393174858807475615943

theorem tailTrace_4394310 : CollatzResearch.WordTrace tailWord_4394310 prefixEnd_4394310 2256393174858807475615943 := by
  unfold tailWord_4394310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008551647192901038864887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106849101806781888829117589 5008551647192901038864887)
  ·
    refine ⟨7512827470789351558297331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5008551647192901038864887 7512827470789351558297331)
    ·
      refine ⟨11269241206184027337445997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7512827470789351558297331 11269241206184027337445997)
      ·
        refine ⟨4225965452319010251542249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11269241206184027337445997 4225965452319010251542249)
        ·
          refine ⟨3169474089239257688656687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4225965452319010251542249 3169474089239257688656687)
          ·
            refine ⟨4754211133858886532985031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169474089239257688656687 4754211133858886532985031)
            ·
              refine ⟨7131316700788329799477547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754211133858886532985031 7131316700788329799477547)
              ·
                refine ⟨10696975051182494699216321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7131316700788329799477547 10696975051182494699216321)
                ·
                  refine ⟨8022731288386871024412241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10696975051182494699216321 8022731288386871024412241)
                  ·
                    refine ⟨6017048466290153268309181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8022731288386871024412241 6017048466290153268309181)
                    ·
                      refine ⟨2256393174858807475615943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6017048466290153268309181 2256393174858807475615943)
                      ·
                        rfl

theorem cell23_4394310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4394310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394310 prefixEnd_4394310 := by exact prefixLift 4394310
  have htrace : WordTrace (prefixWord ++ tailWord_4394310) baseStart_4394310 baseEnd_4394310 := by
    simpa [prefixWord, tailWord_4394310, baseEnd_4394310] using wordTrace_append hprefix tailTrace_4394310
  have hstable : (prefixWord ++ tailWord_4394310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394310).length < 2 ^ (prefixWord ++ tailWord_4394310).sum := by decide
  have hdescent : baseEnd_4394310 < baseStart_4394310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394339 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 2, 4]
def baseStart_4394339 : Nat := 118140960795 + 4394339 * 2 ^ 59
def prefixEnd_4394339 : Nat := 4983230072969 + 3 ^ 40 * 4394339 * 2
def baseEnd_4394339 : Nat := 752136021932595954051103

theorem tailTrace_4394339 : CollatzResearch.WordTrace tailWord_4394339 prefixEnd_4394339 752136021932595954051103 := by
  unfold tailWord_4394339
  simp only [CollatzResearch.WordTrace]
  refine ⟨160274710427067771196482071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106849806951378514130988047 160274710427067771196482071)
  ·
    refine ⟨240412065640601656794723107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160274710427067771196482071 240412065640601656794723107)
    ·
      refine ⟨360618098460902485192084661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240412065640601656794723107 360618098460902485192084661)
      ·
        refine ⟨33807946730709607986757937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 360618098460902485192084661 33807946730709607986757937)
        ·
          refine ⟨25355960048032205990068453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33807946730709607986757937 25355960048032205990068453)
          ·
            refine ⟨4754242509006038623137835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25355960048032205990068453 4754242509006038623137835)
            ·
              refine ⟨7131363763509057934706753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754242509006038623137835 7131363763509057934706753)
              ·
                refine ⟨5348522822631793451030065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7131363763509057934706753 5348522822631793451030065)
                ·
                  refine ⟨4011392116973845088272549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5348522822631793451030065 4011392116973845088272549)
                  ·
                    refine ⟨752136021932595954051103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4011392116973845088272549 752136021932595954051103)
                    ·
                      rfl

theorem cell23_4394339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 4].length) (baseStart_4394339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394339 prefixEnd_4394339 := by exact prefixLift 4394339
  have htrace : WordTrace (prefixWord ++ tailWord_4394339) baseStart_4394339 baseEnd_4394339 := by
    simpa [prefixWord, tailWord_4394339, baseEnd_4394339] using wordTrace_append hprefix tailTrace_4394339
  have hstable : (prefixWord ++ tailWord_4394339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394339).length < 2 ^ (prefixWord ++ tailWord_4394339).sum := by decide
  have hdescent : baseEnd_4394339 < baseStart_4394339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394369 : List Nat := [1, 2, 4, 3, 2, 2, 2, 7]
def baseStart_4394369 : Nat := 118140960795 + 4394369 * 2 ^ 59
def prefixEnd_4394369 : Nat := 4983230072969 + 3 ^ 40 * 4394369 * 2
def baseEnd_4394369 : Nat := 83571239637682323880673

theorem tailTrace_4394369 : CollatzResearch.WordTrace tailWord_4394369 prefixEnd_4394369 83571239637682323880673 := by
  unfold tailWord_4394369
  simp only [CollatzResearch.WordTrace]
  refine ⟨160275804616959086320074161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106850536411306057546716107 160275804616959086320074161)
  ·
    refine ⟨120206853462719314740055621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160275804616959086320074161 120206853462719314740055621)
    ·
      refine ⟨22538785024259871513760429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120206853462719314740055621 22538785024259871513760429)
      ·
        refine ⟨8452044384097451817660161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22538785024259871513760429 8452044384097451817660161)
        ·
          refine ⟨6339033288073088863245121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8452044384097451817660161 6339033288073088863245121)
          ·
            refine ⟨4754274966054816647433841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6339033288073088863245121 4754274966054816647433841)
            ·
              refine ⟨3565706224541112485575381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4754274966054816647433841 3565706224541112485575381)
              ·
                refine ⟨83571239637682323880673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3565706224541112485575381 83571239637682323880673)
                ·
                  rfl

theorem cell23_4394369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 7].length) (baseStart_4394369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394369 prefixEnd_4394369 := by exact prefixLift 4394369
  have htrace : WordTrace (prefixWord ++ tailWord_4394369) baseStart_4394369 baseEnd_4394369 := by
    simpa [prefixWord, tailWord_4394369, baseEnd_4394369] using wordTrace_append hprefix tailTrace_4394369
  have hstable : (prefixWord ++ tailWord_4394369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394369).length < 2 ^ (prefixWord ++ tailWord_4394369).sum := by decide
  have hdescent : baseEnd_4394369 < baseStart_4394369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394375 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_4394375 : Nat := 118140960795 + 4394375 * 2 ^ 59
def prefixEnd_4394375 : Nat := 4983230072969 + 3 ^ 40 * 4394375 * 2
def baseEnd_4394375 : Nat := 2256426551101349721303143

theorem tailTrace_4394375 : CollatzResearch.WordTrace tailWord_4394375 prefixEnd_4394375 2256426551101349721303143 := by
  unfold tailWord_4394375
  simp only [CollatzResearch.WordTrace]
  refine ⟨160276023454937349344792579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106850682303291566229861719 160276023454937349344792579)
  ·
    refine ⟨240414035182406024017188869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160276023454937349344792579 240414035182406024017188869)
    ·
      refine ⟨45077631596701129503222913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240414035182406024017188869 45077631596701129503222913)
      ·
        refine ⟨33808223697525847127417185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45077631596701129503222913 33808223697525847127417185)
        ·
          refine ⟨25356167773144385345562889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33808223697525847127417185 25356167773144385345562889)
          ·
            refine ⟨19017125829858289009172167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25356167773144385345562889 19017125829858289009172167)
            ·
              refine ⟨28525688744787433513758251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19017125829858289009172167 28525688744787433513758251)
              ·
                refine ⟨42788533117181150270637377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28525688744787433513758251 42788533117181150270637377)
                ·
                  refine ⟨32091399837885862702978033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42788533117181150270637377 32091399837885862702978033)
                  ·
                    refine ⟨24068549878414397027233525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32091399837885862702978033 24068549878414397027233525)
                    ·
                      refine ⟨2256426551101349721303143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24068549878414397027233525 2256426551101349721303143)
                      ·
                        rfl

theorem cell23_4394375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_4394375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394375 prefixEnd_4394375 := by exact prefixLift 4394375
  have htrace : WordTrace (prefixWord ++ tailWord_4394375) baseStart_4394375 baseEnd_4394375 := by
    simpa [prefixWord, tailWord_4394375, baseEnd_4394375] using wordTrace_append hprefix tailTrace_4394375
  have hstable : (prefixWord ++ tailWord_4394375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394375).length < 2 ^ (prefixWord ++ tailWord_4394375).sum := by decide
  have hdescent : baseEnd_4394375 < baseStart_4394375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394389 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_4394389 : Nat := 118140960795 + 4394389 * 2 ^ 59
def prefixEnd_4394389 : Nat := 4983230072969 + 3 ^ 40 * 4394389 * 2
def baseEnd_4394389 : Nat := 2256433739830512666528079

theorem tailTrace_4394389 : CollatzResearch.WordTrace tailWord_4394389 prefixEnd_4394389 2256433739830512666528079 := by
  unfold tailWord_4394389
  simp only [CollatzResearch.WordTrace]
  refine ⟨160276534076886629735802221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106851022717924419823868147 160276534076886629735802221)
  ·
    refine ⟨60103700278832486150925833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160276534076886629735802221 60103700278832486150925833)
    ·
      refine ⟨45077775209124364613194375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60103700278832486150925833 45077775209124364613194375)
      ·
        refine ⟨67616662813686546919791563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45077775209124364613194375 67616662813686546919791563)
        ·
          refine ⟨101424994220529820379687345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67616662813686546919791563 101424994220529820379687345)
          ·
            refine ⟨76068745665397365284765509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101424994220529820379687345 76068745665397365284765509)
            ·
              refine ⟨14262889812262005990893533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76068745665397365284765509 14262889812262005990893533)
              ·
                refine ⟨5348583679598252246585075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14262889812262005990893533 5348583679598252246585075)
                ·
                  refine ⟨8022875519397378369877613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5348583679598252246585075 8022875519397378369877613)
                  ·
                    refine ⟨3008578319774016888704105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8022875519397378369877613 3008578319774016888704105)
                    ·
                      refine ⟨2256433739830512666528079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008578319774016888704105 2256433739830512666528079)
                      ·
                        rfl

theorem cell23_4394389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_4394389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394389 prefixEnd_4394389 := by exact prefixLift 4394389
  have htrace : WordTrace (prefixWord ++ tailWord_4394389) baseStart_4394389 baseEnd_4394389 := by
    simpa [prefixWord, tailWord_4394389, baseEnd_4394389] using wordTrace_append hprefix tailTrace_4394389
  have hstable : (prefixWord ++ tailWord_4394389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394389).length < 2 ^ (prefixWord ++ tailWord_4394389).sum := by decide
  have hdescent : baseEnd_4394389 < baseStart_4394389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394413 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4394413 : Nat := 118140960795 + 4394413 * 2 ^ 59
def prefixEnd_4394413 : Nat := 4983230072969 + 3 ^ 40 * 4394413 * 2
def baseEnd_4394413 : Nat := 2256446063366220572627969

theorem tailTrace_4394413 : CollatzResearch.WordTrace tailWord_4394413 prefixEnd_4394413 2256446063366220572627969 := by
  unfold tailWord_4394413
  simp only [CollatzResearch.WordTrace]
  refine ⟨160277409428799681834675893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106851606285866454556450595 160277409428799681834675893)
  ·
    refine ⟨15026007133949970172000865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160277409428799681834675893 15026007133949970172000865)
    ·
      refine ⟨11269505350462477629000649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15026007133949970172000865 11269505350462477629000649)
      ·
        refine ⟨8452129012846858221750487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11269505350462477629000649 8452129012846858221750487)
        ·
          refine ⟨12678193519270287332625731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8452129012846858221750487 12678193519270287332625731)
          ·
            refine ⟨19017290278905430998938597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12678193519270287332625731 19017290278905430998938597)
            ·
              refine ⟨3565741927294768312300987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19017290278905430998938597 3565741927294768312300987)
              ·
                refine ⟨5348612890942152468451481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565741927294768312300987 5348612890942152468451481)
                ·
                  refine ⟨4011459668206614351338611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5348612890942152468451481 4011459668206614351338611)
                  ·
                    refine ⟨6017189502309921527007917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4011459668206614351338611 6017189502309921527007917)
                    ·
                      refine ⟨2256446063366220572627969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6017189502309921527007917 2256446063366220572627969)
                      ·
                        rfl

theorem cell23_4394413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4394413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394413 prefixEnd_4394413 := by exact prefixLift 4394413
  have htrace : WordTrace (prefixWord ++ tailWord_4394413) baseStart_4394413 baseEnd_4394413 := by
    simpa [prefixWord, tailWord_4394413, baseEnd_4394413] using wordTrace_append hprefix tailTrace_4394413
  have hstable : (prefixWord ++ tailWord_4394413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394413).length < 2 ^ (prefixWord ++ tailWord_4394413).sum := by decide
  have hdescent : baseEnd_4394413 < baseStart_4394413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394415 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_4394415 : Nat := 118140960795 + 4394415 * 2 ^ 59
def prefixEnd_4394415 : Nat := 4983230072969 + 3 ^ 40 * 4394415 * 2
def baseEnd_4394415 : Nat := 2256447090327529564802959

theorem tailTrace_4394415 : CollatzResearch.WordTrace tailWord_4394415 prefixEnd_4394415 2256447090327529564802959 := by
  unfold tailWord_4394415
  simp only [CollatzResearch.WordTrace]
  refine ⟨160277482374792436176248699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106851654916528290784165799 160277482374792436176248699)
  ·
    refine ⟨240416223562188654264373049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160277482374792436176248699 240416223562188654264373049)
    ·
      refine ⟨180312167671641490698279787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240416223562188654264373049 180312167671641490698279787)
      ·
        refine ⟨270468251507462236047419681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180312167671641490698279787 270468251507462236047419681)
        ·
          refine ⟨202851188630596677035564761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270468251507462236047419681 202851188630596677035564761)
          ·
            refine ⟨152138391472947507776673571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202851188630596677035564761 152138391472947507776673571)
            ·
              refine ⟨228207587209421261665010357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152138391472947507776673571 228207587209421261665010357)
              ·
                refine ⟨21394461300883243281094721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228207587209421261665010357 21394461300883243281094721)
                ·
                  refine ⟨16045845975662432460821041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21394461300883243281094721 16045845975662432460821041)
                  ·
                    refine ⟨12034384481746824345615781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16045845975662432460821041 12034384481746824345615781)
                    ·
                      refine ⟨2256447090327529564802959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12034384481746824345615781 2256447090327529564802959)
                      ·
                        rfl

theorem cell23_4394415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_4394415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394415 prefixEnd_4394415 := by exact prefixLift 4394415
  have htrace : WordTrace (prefixWord ++ tailWord_4394415) baseStart_4394415 baseEnd_4394415 := by
    simpa [prefixWord, tailWord_4394415, baseEnd_4394415] using wordTrace_append hprefix tailTrace_4394415
  have hstable : (prefixWord ++ tailWord_4394415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394415).length < 2 ^ (prefixWord ++ tailWord_4394415).sum := by decide
  have hdescent : baseEnd_4394415 < baseStart_4394415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394436 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_4394436 : Nat := 118140960795 + 4394436 * 2 ^ 59
def prefixEnd_4394436 : Nat := 4983230072969 + 3 ^ 40 * 4394436 * 2
def baseEnd_4394436 : Nat := 2256457873421273982640363

theorem tailTrace_4394436 : CollatzResearch.WordTrace tailWord_4394436 prefixEnd_4394436 2256457873421273982640363 := by
  unfold tailWord_4394436
  simp only [CollatzResearch.WordTrace]
  refine ⟨80139124153858178381381581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106852165538477571175175441 80139124153858178381381581)
  ·
    refine ⟨30052171557696816893018093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80139124153858178381381581 30052171557696816893018093)
    ·
      refine ⟨11269564334136306334881785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30052171557696816893018093 11269564334136306334881785)
      ·
        refine ⟨8452173250602229751161339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11269564334136306334881785 8452173250602229751161339)
        ·
          refine ⟨12678259875903344626742009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8452173250602229751161339 12678259875903344626742009)
          ·
            refine ⟨9508694906927508470056507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12678259875903344626742009 9508694906927508470056507)
            ·
              refine ⟨14263042360391262705084761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9508694906927508470056507 14263042360391262705084761)
              ·
                refine ⟨10697281770293447028813571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14263042360391262705084761 10697281770293447028813571)
                ·
                  refine ⟨16045922655440170543220357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10697281770293447028813571 16045922655440170543220357)
                  ·
                    refine ⟨3008610497895031976853817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16045922655440170543220357 3008610497895031976853817)
                    ·
                      refine ⟨2256457873421273982640363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008610497895031976853817 2256457873421273982640363)
                      ·
                        rfl

theorem cell23_4394436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_4394436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394436 prefixEnd_4394436 := by exact prefixLift 4394436
  have htrace : WordTrace (prefixWord ++ tailWord_4394436) baseStart_4394436 baseEnd_4394436 := by
    simpa [prefixWord, tailWord_4394436, baseEnd_4394436] using wordTrace_append hprefix tailTrace_4394436
  have hstable : (prefixWord ++ tailWord_4394436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394436).length < 2 ^ (prefixWord ++ tailWord_4394436).sum := by decide
  have hdescent : baseEnd_4394436 < baseStart_4394436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394469 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4394469 : Nat := 118140960795 + 4394469 * 2 ^ 59
def prefixEnd_4394469 : Nat := 4983230072969 + 3 ^ 40 * 4394469 * 2
def baseEnd_4394469 : Nat := 2256474818282872353527711

theorem tailTrace_4394469 : CollatzResearch.WordTrace tailWord_4394469 prefixEnd_4394469 2256474818282872353527711 := by
  unfold tailWord_4394469
  simp only [CollatzResearch.WordTrace]
  refine ⟨160279451916596803398714461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106852967944397868932476307 160279451916596803398714461)
  ·
    refine ⟨60104794468723801274517923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160279451916596803398714461 60104794468723801274517923)
    ·
      refine ⟨90157191703085701911776885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60104794468723801274517923 90157191703085701911776885)
      ·
        refine ⟨8452236722164284554229083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90157191703085701911776885 8452236722164284554229083)
        ·
          refine ⟨12678355083246426831343625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8452236722164284554229083 12678355083246426831343625)
          ·
            refine ⟨9508766312434820123507719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12678355083246426831343625 9508766312434820123507719)
            ·
              refine ⟨14263149468652230185261579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9508766312434820123507719 14263149468652230185261579)
              ·
                refine ⟨21394724202978345277892369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14263149468652230185261579 21394724202978345277892369)
                ·
                  refine ⟨16046043152233758958419277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21394724202978345277892369 16046043152233758958419277)
                  ·
                    refine ⟨6017266182087659609407229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16046043152233758958419277 6017266182087659609407229)
                    ·
                      refine ⟨2256474818282872353527711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6017266182087659609407229 2256474818282872353527711)
                      ·
                        rfl

theorem cell23_4394469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4394469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394469 prefixEnd_4394469 := by exact prefixLift 4394469
  have htrace : WordTrace (prefixWord ++ tailWord_4394469) baseStart_4394469 baseEnd_4394469 := by
    simpa [prefixWord, tailWord_4394469, baseEnd_4394469] using wordTrace_append hprefix tailTrace_4394469
  have hstable : (prefixWord ++ tailWord_4394469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394469).length < 2 ^ (prefixWord ++ tailWord_4394469).sum := by decide
  have hdescent : baseEnd_4394469 < baseStart_4394469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394495 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_4394495 : Nat := 118140960795 + 4394495 * 2 ^ 59
def prefixEnd_4394495 : Nat := 4983230072969 + 3 ^ 40 * 4394495 * 2
def baseEnd_4394495 : Nat := 2256488168779889251802591

theorem tailTrace_4394495 : CollatzResearch.WordTrace tailWord_4394495 prefixEnd_4394495 2256488168779889251802591 := by
  unfold tailWord_4394495
  simp only [CollatzResearch.WordTrace]
  refine ⟨160280400214502609839160939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106853600143001739892773959 160280400214502609839160939)
  ·
    refine ⟨240420600321753914758741409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160280400214502609839160939 240420600321753914758741409)
    ·
      refine ⟨180315450241315436069056057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240420600321753914758741409 180315450241315436069056057)
      ·
        refine ⟨135236587680986577051792043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180315450241315436069056057 135236587680986577051792043)
        ·
          refine ⟨202854881521479865577688065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135236587680986577051792043 202854881521479865577688065)
          ·
            refine ⟨152141161141109899183266049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202854881521479865577688065 152141161141109899183266049)
            ·
              refine ⟨114105870855832424387449537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152141161141109899183266049 114105870855832424387449537)
              ·
                refine ⟨85579403141874318290587153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114105870855832424387449537 85579403141874318290587153)
                ·
                  refine ⟨64184552356405738717940365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85579403141874318290587153 64184552356405738717940365)
                  ·
                    refine ⟨24069207133652152019227637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64184552356405738717940365 24069207133652152019227637)
                    ·
                      refine ⟨2256488168779889251802591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24069207133652152019227637 2256488168779889251802591)
                      ·
                        rfl

theorem cell23_4394495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_4394495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394495 prefixEnd_4394495 := by exact prefixLift 4394495
  have htrace : WordTrace (prefixWord ++ tailWord_4394495) baseStart_4394495 baseEnd_4394495 := by
    simpa [prefixWord, tailWord_4394495, baseEnd_4394495] using wordTrace_append hprefix tailTrace_4394495
  have hstable : (prefixWord ++ tailWord_4394495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394495).length < 2 ^ (prefixWord ++ tailWord_4394495).sum := by decide
  have hdescent : baseEnd_4394495 < baseStart_4394495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394505 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_4394505 : Nat := 118140960795 + 4394505 * 2 ^ 59
def prefixEnd_4394505 : Nat := 4983230072969 + 3 ^ 40 * 4394505 * 2
def baseEnd_4394505 : Nat := 2256493303586434212677545

theorem tailTrace_4394505 : CollatzResearch.WordTrace tailWord_4394505 prefixEnd_4394505 2256493303586434212677545 := by
  unfold tailWord_4394505
  simp only [CollatzResearch.WordTrace]
  refine ⟨160280764944466381547024969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106853843296310921031349979 160280764944466381547024969)
  ·
    refine ⟨120210573708349786160268727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160280764944466381547024969 120210573708349786160268727)
    ·
      refine ⟨180315860562524679240403091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120210573708349786160268727 180315860562524679240403091)
      ·
        refine ⟨270473790843787018860604637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180315860562524679240403091 270473790843787018860604637)
        ·
          refine ⟨101427671566420132072726739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270473790843787018860604637 101427671566420132072726739)
          ·
            refine ⟨152141507349630198109090109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101427671566420132072726739 152141507349630198109090109)
            ·
              refine ⟨57053065256111324290908791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152141507349630198109090109 57053065256111324290908791)
              ·
                refine ⟨85579597884166986436363187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57053065256111324290908791 85579597884166986436363187)
                ·
                  refine ⟨128369396826250479654544781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85579597884166986436363187 128369396826250479654544781)
                  ·
                    refine ⟨48138523809843929870454293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128369396826250479654544781 48138523809843929870454293)
                    ·
                      refine ⟨2256493303586434212677545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48138523809843929870454293 2256493303586434212677545)
                      ·
                        rfl

theorem cell23_4394505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_4394505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394505 prefixEnd_4394505 := by exact prefixLift 4394505
  have htrace : WordTrace (prefixWord ++ tailWord_4394505) baseStart_4394505 baseEnd_4394505 := by
    simpa [prefixWord, tailWord_4394505, baseEnd_4394505] using wordTrace_append hprefix tailTrace_4394505
  have hstable : (prefixWord ++ tailWord_4394505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394505).length < 2 ^ (prefixWord ++ tailWord_4394505).sum := by decide
  have hdescent : baseEnd_4394505 < baseStart_4394505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394553 : List Nat := [1, 2, 1, 5, 1, 4, 1, 3, 1, 4]
def baseStart_4394553 : Nat := 118140960795 + 4394553 * 2 ^ 59
def prefixEnd_4394553 : Nat := 4983230072969 + 3 ^ 40 * 4394553 * 2
def baseEnd_4394553 : Nat := 752172650219283341625775

theorem tailTrace_4394553 : CollatzResearch.WordTrace tailWord_4394553 prefixEnd_4394553 752172650219283341625775 := by
  unfold tailWord_4394553
  simp only [CollatzResearch.WordTrace]
  refine ⟨160282515648292485744772313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106855010432194990496514875 160282515648292485744772313)
  ·
    refine ⟨120211886736219364308579235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160282515648292485744772313 120211886736219364308579235)
    ·
      refine ⟨180317830104329046462868853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120211886736219364308579235 180317830104329046462868853)
      ·
        refine ⟨16904796572280848105893955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180317830104329046462868853 16904796572280848105893955)
        ·
          refine ⟨25357194858421272158840933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16904796572280848105893955 25357194858421272158840933)
          ·
            refine ⟨4754474035953988529782675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25357194858421272158840933 4754474035953988529782675)
            ·
              refine ⟨7131711053930982794674013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754474035953988529782675 7131711053930982794674013)
              ·
                refine ⟨2674391645224118548002755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7131711053930982794674013 2674391645224118548002755)
                ·
                  refine ⟨4011587467836177822004133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674391645224118548002755 4011587467836177822004133)
                  ·
                    refine ⟨752172650219283341625775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4011587467836177822004133 752172650219283341625775)
                    ·
                      rfl

theorem cell23_4394553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 4].length) (baseStart_4394553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394553 prefixEnd_4394553 := by exact prefixLift 4394553
  have htrace : WordTrace (prefixWord ++ tailWord_4394553) baseStart_4394553 baseEnd_4394553 := by
    simpa [prefixWord, tailWord_4394553, baseEnd_4394553] using wordTrace_append hprefix tailTrace_4394553
  have hstable : (prefixWord ++ tailWord_4394553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394553).length < 2 ^ (prefixWord ++ tailWord_4394553).sum := by decide
  have hdescent : baseEnd_4394553 < baseStart_4394553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394592 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 1, 6]
def baseStart_4394592 : Nat := 118140960795 + 4394592 * 2 ^ 59
def prefixEnd_4394592 : Nat := 4983230072969 + 3 ^ 40 * 4394592 * 2
def baseEnd_4394592 : Nat := 752179325467791790763215

theorem tailTrace_4394592 : CollatzResearch.WordTrace tailWord_4394592 prefixEnd_4394592 752179325467791790763215 := by
  unfold tailWord_4394592
  simp only [CollatzResearch.WordTrace]
  refine ⟨80141969047575597702721015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106855958730100796936961353 80141969047575597702721015)
  ·
    refine ⟨120212953571363396554081523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80141969047575597702721015 120212953571363396554081523)
    ·
      refine ⟨180319430357045094831122285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120212953571363396554081523 180319430357045094831122285)
      ·
        refine ⟨67619786383891910561670857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180319430357045094831122285 67619786383891910561670857)
        ·
          refine ⟨50714839787918932921253143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67619786383891910561670857 50714839787918932921253143)
          ·
            refine ⟨76072259681878399381879715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50714839787918932921253143 76072259681878399381879715)
            ·
              refine ⟨114108389522817599072819573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76072259681878399381879715 114108389522817599072819573)
              ·
                refine ⟨10697661517764149913076835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114108389522817599072819573 10697661517764149913076835)
                ·
                  refine ⟨16046492276646224869615253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10697661517764149913076835 16046492276646224869615253)
                  ·
                    refine ⟨752179325467791790763215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16046492276646224869615253 752179325467791790763215)
                    ·
                      rfl

theorem cell23_4394592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_4394592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394592 prefixEnd_4394592 := by exact prefixLift 4394592
  have htrace : WordTrace (prefixWord ++ tailWord_4394592) baseStart_4394592 baseEnd_4394592 := by
    simpa [prefixWord, tailWord_4394592, baseEnd_4394592] using wordTrace_append hprefix tailTrace_4394592
  have hstable : (prefixWord ++ tailWord_4394592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394592).length < 2 ^ (prefixWord ++ tailWord_4394592).sum := by decide
  have hdescent : baseEnd_4394592 < baseStart_4394592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394596 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_4394596 : Nat := 118140960795 + 4394596 * 2 ^ 59
def prefixEnd_4394596 : Nat := 4983230072969 + 3 ^ 40 * 4394596 * 2
def baseEnd_4394596 : Nat := 752180010108664452213209

theorem tailTrace_4394596 : CollatzResearch.WordTrace tailWord_4394596 prefixEnd_4394596 752180010108664452213209 := by
  unfold tailWord_4394596
  simp only [CollatzResearch.WordTrace]
  refine ⟨80142041993568352044293821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106856055991424469392391761 80142041993568352044293821)
  ·
    refine ⟨30053265747588132016610183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80142041993568352044293821 30053265747588132016610183)
    ·
      refine ⟨45079898621382198024915275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30053265747588132016610183 45079898621382198024915275)
      ·
        refine ⟨67619847932073297037372913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45079898621382198024915275 67619847932073297037372913)
        ·
          refine ⟨50714885949054972778029685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67619847932073297037372913 50714885949054972778029685)
          ·
            refine ⟨4754520557723903697940283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50714885949054972778029685 4754520557723903697940283)
            ·
              refine ⟨7131780836585855546910425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754520557723903697940283 7131780836585855546910425)
              ·
                refine ⟨5348835627439391660182819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7131780836585855546910425 5348835627439391660182819)
                ·
                  refine ⟨8023253441159087490274229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5348835627439391660182819 8023253441159087490274229)
                  ·
                    refine ⟨752180010108664452213209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8023253441159087490274229 752180010108664452213209)
                    ·
                      rfl

theorem cell23_4394596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_4394596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394596 prefixEnd_4394596 := by exact prefixLift 4394596
  have htrace : WordTrace (prefixWord ++ tailWord_4394596) baseStart_4394596 baseEnd_4394596 := by
    simpa [prefixWord, tailWord_4394596, baseEnd_4394596] using wordTrace_append hprefix tailTrace_4394596
  have hstable : (prefixWord ++ tailWord_4394596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394596).length < 2 ^ (prefixWord ++ tailWord_4394596).sum := by decide
  have hdescent : baseEnd_4394596 < baseStart_4394596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394599 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_4394599 : Nat := 118140960795 + 4394599 * 2 ^ 59
def prefixEnd_4394599 : Nat := 4983230072969 + 3 ^ 40 * 4394599 * 2
def baseEnd_4394599 : Nat := 2256541570767956844902113

theorem tailTrace_4394599 : CollatzResearch.WordTrace tailWord_4394599 prefixEnd_4394599 2256541570767956844902113 := by
  unfold tailWord_4394599
  simp only [CollatzResearch.WordTrace]
  refine ⟨160284193406125835600946851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106856128937417223733964567 160284193406125835600946851)
  ·
    refine ⟨240426290109188753401420277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160284193406125835600946851 240426290109188753401420277)
    ·
      refine ⟨22539964697736445631383151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 240426290109188753401420277 22539964697736445631383151)
      ·
        refine ⟨33809947046604668447074727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22539964697736445631383151 33809947046604668447074727)
        ·
          refine ⟨50714920569907002670612091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33809947046604668447074727 50714920569907002670612091)
          ·
            refine ⟨76072380854860504005918137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50714920569907002670612091 76072380854860504005918137)
            ·
              refine ⟨57054285641145378004438603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76072380854860504005918137 57054285641145378004438603)
              ·
                refine ⟨85581428461718067006657905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57054285641145378004438603 85581428461718067006657905)
                ·
                  refine ⟨64186071346288550254993429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85581428461718067006657905 64186071346288550254993429)
                  ·
                    refine ⟨3008722094357275793202817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64186071346288550254993429 3008722094357275793202817)
                    ·
                      refine ⟨2256541570767956844902113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008722094357275793202817 2256541570767956844902113)
                      ·
                        rfl

theorem cell23_4394599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_4394599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394599 prefixEnd_4394599 := by exact prefixLift 4394599
  have htrace : WordTrace (prefixWord ++ tailWord_4394599) baseStart_4394599 baseEnd_4394599 := by
    simpa [prefixWord, tailWord_4394599, baseEnd_4394599] using wordTrace_append hprefix tailTrace_4394599
  have hstable : (prefixWord ++ tailWord_4394599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394599).length < 2 ^ (prefixWord ++ tailWord_4394599).sum := by decide
  have hdescent : baseEnd_4394599 < baseStart_4394599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394613 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4394613 : Nat := 118140960795 + 4394613 * 2 ^ 59
def prefixEnd_4394613 : Nat := 4983230072969 + 3 ^ 40 * 4394613 * 2
def baseEnd_4394613 : Nat := 752182919832373263375683

theorem tailTrace_4394613 : CollatzResearch.WordTrace tailWord_4394613 prefixEnd_4394613 752182919832373263375683 := by
  unfold tailWord_4394613
  simp only [CollatzResearch.WordTrace]
  refine ⟨160284704028075115991956493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106856469352050077327970995 160284704028075115991956493)
  ·
    refine ⟨60106764010528168496983685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160284704028075115991956493 60106764010528168496983685)
    ·
      refine ⟨11270018251974031593184441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60106764010528168496983685 11270018251974031593184441)
      ·
        refine ⟨8452513688980523694888331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11270018251974031593184441 8452513688980523694888331)
        ·
          refine ⟨12678770533470785542332497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8452513688980523694888331 12678770533470785542332497)
          ·
            refine ⟨9509077900103089156749373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12678770533470785542332497 9509077900103089156749373)
            ·
              refine ⟨3565904212538658433781015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9509077900103089156749373 3565904212538658433781015)
              ·
                refine ⟨5348856318807987650671523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565904212538658433781015 5348856318807987650671523)
                ·
                  refine ⟨8023284478211981476007285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5348856318807987650671523 8023284478211981476007285)
                  ·
                    refine ⟨752182919832373263375683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8023284478211981476007285 752182919832373263375683)
                    ·
                      rfl

theorem cell23_4394613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4394613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394613 prefixEnd_4394613 := by exact prefixLift 4394613
  have htrace : WordTrace (prefixWord ++ tailWord_4394613) baseStart_4394613 baseEnd_4394613 := by
    simpa [prefixWord, tailWord_4394613, baseEnd_4394613] using wordTrace_append hprefix tailTrace_4394613
  have hstable : (prefixWord ++ tailWord_4394613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394613).length < 2 ^ (prefixWord ++ tailWord_4394613).sum := by decide
  have hdescent : baseEnd_4394613 < baseStart_4394613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394664 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4394664 : Nat := 118140960795 + 4394664 * 2 ^ 59
def prefixEnd_4394664 : Nat := 4983230072969 + 3 ^ 40 * 4394664 * 2
def baseEnd_4394664 : Nat := 752191649003499696863105

theorem tailTrace_4394664 : CollatzResearch.WordTrace tailWord_4394664 prefixEnd_4394664 752191649003499696863105 := by
  unfold tailWord_4394664
  simp only [CollatzResearch.WordTrace]
  refine ⟨80143282075445175851031523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106857709433926901134708697 80143282075445175851031523)
  ·
    refine ⟨120214923113167763776547285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80143282075445175851031523 120214923113167763776547285)
    ·
      refine ⟨2817537260464869463512827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 120214923113167763776547285 2817537260464869463512827)
      ·
        refine ⟨4226305890697304195269241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817537260464869463512827 4226305890697304195269241)
        ·
          refine ⟨3169729418022978146451931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4226305890697304195269241 3169729418022978146451931)
          ·
            refine ⟨4754594127034467219677897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169729418022978146451931 4754594127034467219677897)
            ·
              refine ⟨3565945595275850414758423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4754594127034467219677897 3565945595275850414758423)
              ·
                refine ⟨5348918392913775622137635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565945595275850414758423 5348918392913775622137635)
                ·
                  refine ⟨8023377589370663433206453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5348918392913775622137635 8023377589370663433206453)
                  ·
                    refine ⟨752191649003499696863105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8023377589370663433206453 752191649003499696863105)
                    ·
                      rfl

theorem cell23_4394664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4394664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394664 prefixEnd_4394664 := by exact prefixLift 4394664
  have htrace : WordTrace (prefixWord ++ tailWord_4394664) baseStart_4394664 baseEnd_4394664 := by
    simpa [prefixWord, tailWord_4394664, baseEnd_4394664] using wordTrace_append hprefix tailTrace_4394664
  have hstable : (prefixWord ++ tailWord_4394664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394664).length < 2 ^ (prefixWord ++ tailWord_4394664).sum := by decide
  have hdescent : baseEnd_4394664 < baseStart_4394664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394670 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4394670 : Nat := 118140960795 + 4394670 * 2 ^ 59
def prefixEnd_4394670 : Nat := 4983230072969 + 3 ^ 40 * 4394670 * 2
def baseEnd_4394670 : Nat := 2256578027894426067114287

theorem tailTrace_4394670 : CollatzResearch.WordTrace tailWord_4394670 prefixEnd_4394670 2256578027894426067114287 := by
  unfold tailWord_4394670
  simp only [CollatzResearch.WordTrace]
  refine ⟨20035847873608576840847683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106857855325912409817854309 20035847873608576840847683)
  ·
    refine ⟨30053771810412865261271525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20035847873608576840847683 30053771810412865261271525)
    ·
      refine ⟨5635082214452412236488411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30053771810412865261271525 5635082214452412236488411)
      ·
        refine ⟨8452623321678618354732617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5635082214452412236488411 8452623321678618354732617)
        ·
          refine ⟨6339467491258963766049463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8452623321678618354732617 6339467491258963766049463)
          ·
            refine ⟨9509201236888445649074195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6339467491258963766049463 9509201236888445649074195)
            ·
              refine ⟨14263801855332668473611293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9509201236888445649074195 14263801855332668473611293)
              ·
                refine ⟨5348925695749750677604235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14263801855332668473611293 5348925695749750677604235)
                ·
                  refine ⟨8023388543624626016406353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5348925695749750677604235 8023388543624626016406353)
                  ·
                    refine ⟨6017541407718469512304765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8023388543624626016406353 6017541407718469512304765)
                    ·
                      refine ⟨2256578027894426067114287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6017541407718469512304765 2256578027894426067114287)
                      ·
                        rfl

theorem cell23_4394670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4394670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394670 prefixEnd_4394670 := by exact prefixLift 4394670
  have htrace : WordTrace (prefixWord ++ tailWord_4394670) baseStart_4394670 baseEnd_4394670 := by
    simpa [prefixWord, tailWord_4394670, baseEnd_4394670] using wordTrace_append hprefix tailTrace_4394670
  have hstable : (prefixWord ++ tailWord_4394670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394670).length < 2 ^ (prefixWord ++ tailWord_4394670).sum := by decide
  have hdescent : baseEnd_4394670 < baseStart_4394670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394700 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4394700 : Nat := 118140960795 + 4394700 * 2 ^ 59
def prefixEnd_4394700 : Nat := 4983230072969 + 3 ^ 40 * 4394700 * 2
def baseEnd_4394700 : Nat := 2256593432314060949739149

theorem tailTrace_4394700 : CollatzResearch.WordTrace tailWord_4394700 prefixEnd_4394700 2256593432314060949739149 := by
  unfold tailWord_4394700
  simp only [CollatzResearch.WordTrace]
  refine ⟨80143938589379964925186777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106858584785839953233582369 80143938589379964925186777)
  ·
    refine ⟨60107953942034973693890083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80143938589379964925186777 60107953942034973693890083)
    ·
      refine ⟨90161930913052460540835125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60107953942034973693890083 90161930913052460540835125)
      ·
        refine ⟨8452681023098668175703293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90161930913052460540835125 8452681023098668175703293)
        ·
          refine ⟨3169755383662000565888735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8452681023098668175703293 3169755383662000565888735)
          ·
            refine ⟨4754633075493000848833103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169755383662000565888735 4754633075493000848833103)
            ·
              refine ⟨7131949613239501273249655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754633075493000848833103 7131949613239501273249655)
              ·
                refine ⟨10697924419859251909874483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7131949613239501273249655 10697924419859251909874483)
                ·
                  refine ⟨16046886629788877864811725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10697924419859251909874483 16046886629788877864811725)
                  ·
                    refine ⟨6017582486170829199304397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16046886629788877864811725 6017582486170829199304397)
                    ·
                      refine ⟨2256593432314060949739149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6017582486170829199304397 2256593432314060949739149)
                      ·
                        rfl

theorem cell23_4394700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4394700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394700 prefixEnd_4394700 := by exact prefixLift 4394700
  have htrace : WordTrace (prefixWord ++ tailWord_4394700) baseStart_4394700 baseEnd_4394700 := by
    simpa [prefixWord, tailWord_4394700, baseEnd_4394700] using wordTrace_append hprefix tailTrace_4394700
  have hstable : (prefixWord ++ tailWord_4394700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394700).length < 2 ^ (prefixWord ++ tailWord_4394700).sum := by decide
  have hdescent : baseEnd_4394700 < baseStart_4394700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394739 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 3]
def baseStart_4394739 : Nat := 118140960795 + 4394739 * 2 ^ 59
def prefixEnd_4394739 : Nat := 4983230072969 + 3 ^ 40 * 4394739 * 2
def baseEnd_4394739 : Nat := 2256613458059586297151469

theorem tailTrace_4394739 : CollatzResearch.WordTrace tailWord_4394739 prefixEnd_4394739 2256613458059586297151469 := by
  unfold tailWord_4394739
  simp only [CollatzResearch.WordTrace]
  refine ⟨160289299625618639511043271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106859533083745759674028847 160289299625618639511043271)
  ·
    refine ⟨240433949438427959266564907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160289299625618639511043271 240433949438427959266564907)
    ·
      refine ⟨360650924157641938899847361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240433949438427959266564907 360650924157641938899847361)
      ·
        refine ⟨270488193118231454174885521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360650924157641938899847361 270488193118231454174885521)
        ·
          refine ⟨202866144838673590631164141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270488193118231454174885521 202866144838673590631164141)
          ·
            refine ⟨76074804314502596486686553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202866144838673590631164141 76074804314502596486686553)
            ·
              refine ⟨57056103235876947365014915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76074804314502596486686553 57056103235876947365014915)
              ·
                refine ⟨85584154853815421047522373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57056103235876947365014915 85584154853815421047522373)
                ·
                  refine ⟨16047029035090391446410445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85584154853815421047522373 16047029035090391446410445)
                  ·
                    refine ⟨6017635888158896792403917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16047029035090391446410445 6017635888158896792403917)
                    ·
                      refine ⟨2256613458059586297151469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6017635888158896792403917 2256613458059586297151469)
                      ·
                        rfl

theorem cell23_4394739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_4394739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394739 prefixEnd_4394739 := by exact prefixLift 4394739
  have htrace : WordTrace (prefixWord ++ tailWord_4394739) baseStart_4394739 baseEnd_4394739 := by
    simpa [prefixWord, tailWord_4394739, baseEnd_4394739] using wordTrace_append hprefix tailTrace_4394739
  have hstable : (prefixWord ++ tailWord_4394739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394739).length < 2 ^ (prefixWord ++ tailWord_4394739).sum := by decide
  have hdescent : baseEnd_4394739 < baseStart_4394739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394779 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 4]
def baseStart_4394779 : Nat := 118140960795 + 4394779 * 2 ^ 59
def prefixEnd_4394779 : Nat := 4983230072969 + 3 ^ 40 * 4394779 * 2
def baseEnd_4394779 : Nat := 2256633997285766140651285

theorem tailTrace_4394779 : CollatzResearch.WordTrace tailWord_4394779 prefixEnd_4394779 2256633997285766140651285 := by
  unfold tailWord_4394779
  simp only [CollatzResearch.WordTrace]
  refine ⟨160290758545473726342499391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106860505696982484228332927 160290758545473726342499391)
  ·
    refine ⟨240436137818210589513749087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160290758545473726342499391 240436137818210589513749087)
    ·
      refine ⟨360654206727315884270623631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240436137818210589513749087 360654206727315884270623631)
      ·
        refine ⟨540981310090973826405935447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360654206727315884270623631 540981310090973826405935447)
        ·
          refine ⟨811471965136460739608903171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540981310090973826405935447 811471965136460739608903171)
          ·
            refine ⟨1217207947704691109413354757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811471965136460739608903171 1217207947704691109413354757)
            ·
              refine ⟨228226490194629583015004017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1217207947704691109413354757 228226490194629583015004017)
              ·
                refine ⟨171169867645972187261253013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228226490194629583015004017 171169867645972187261253013)
                ·
                  refine ⟨8023587545904946277871235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171169867645972187261253013 8023587545904946277871235)
                  ·
                    refine ⟨12035381318857419416806853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8023587545904946277871235 12035381318857419416806853)
                    ·
                      refine ⟨2256633997285766140651285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12035381318857419416806853 2256633997285766140651285)
                      ·
                        rfl

theorem cell23_4394779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 4].length) (baseStart_4394779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394779 prefixEnd_4394779 := by exact prefixLift 4394779
  have htrace : WordTrace (prefixWord ++ tailWord_4394779) baseStart_4394779 baseEnd_4394779 := by
    simpa [prefixWord, tailWord_4394779, baseEnd_4394779] using wordTrace_append hprefix tailTrace_4394779
  have hstable : (prefixWord ++ tailWord_4394779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394779).length < 2 ^ (prefixWord ++ tailWord_4394779).sum := by decide
  have hdescent : baseEnd_4394779 < baseStart_4394779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394796 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_4394796 : Nat := 118140960795 + 4394796 * 2 ^ 59
def prefixEnd_4394796 : Nat := 4983230072969 + 3 ^ 40 * 4394796 * 2
def baseEnd_4394796 : Nat := 2256642726456892574138707

theorem tailTrace_4394796 : CollatzResearch.WordTrace tailWord_4394796 prefixEnd_4394796 2256642726456892574138707 := by
  unfold tailWord_4394796
  simp only [CollatzResearch.WordTrace]
  refine ⟨80145689293206069122934121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106860919057608092163912161 80145689293206069122934121)
  ·
    refine ⟨60109266969904551842200591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80145689293206069122934121 60109266969904551842200591)
    ·
      refine ⟨90163900454856827763300887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60109266969904551842200591 90163900454856827763300887)
      ·
        refine ⟨135245850682285241644951331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90163900454856827763300887 135245850682285241644951331)
        ·
          refine ⟨202868776023427862467426997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135245850682285241644951331 202868776023427862467426997)
          ·
            refine ⟨19018947752196362106321281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 202868776023427862467426997 19018947752196362106321281)
            ·
              refine ⟨14264210814147271579740961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19018947752196362106321281 14264210814147271579740961)
              ·
                refine ⟨10698158110610453684805721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14264210814147271579740961 10698158110610453684805721)
                ·
                  refine ⟨8023618582957840263604291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10698158110610453684805721 8023618582957840263604291)
                  ·
                    refine ⟨12035427874436760395406437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8023618582957840263604291 12035427874436760395406437)
                    ·
                      refine ⟨2256642726456892574138707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12035427874436760395406437 2256642726456892574138707)
                      ·
                        rfl

theorem cell23_4394796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_4394796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394796 prefixEnd_4394796 := by exact prefixLift 4394796
  have htrace : WordTrace (prefixWord ++ tailWord_4394796) baseStart_4394796 baseEnd_4394796 := by
    simpa [prefixWord, tailWord_4394796, baseEnd_4394796] using wordTrace_append hprefix tailTrace_4394796
  have hstable : (prefixWord ++ tailWord_4394796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394796).length < 2 ^ (prefixWord ++ tailWord_4394796).sum := by decide
  have hdescent : baseEnd_4394796 < baseStart_4394796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394813 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4394813 : Nat := 118140960795 + 4394813 * 2 ^ 59
def prefixEnd_4394813 : Nat := 4983230072969 + 3 ^ 40 * 4394813 * 2
def baseEnd_4394813 : Nat := 2256651455628019007626129

theorem tailTrace_4394813 : CollatzResearch.WordTrace tailWord_4394813 prefixEnd_4394813 2256651455628019007626129 := by
  unfold tailWord_4394813
  simp only [CollatzResearch.WordTrace]
  refine ⟨160291998627350550149237093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106861332418233700099491395 160291998627350550149237093)
  ·
    refine ⟨30054749742628228152981955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160291998627350550149237093 30054749742628228152981955)
    ·
      refine ⟨45082124613942342229472933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30054749742628228152981955 45082124613942342229472933)
      ·
        refine ⟨8452898365114189168026175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45082124613942342229472933 8452898365114189168026175)
        ·
          refine ⟨12679347547671283752039263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8452898365114189168026175 12679347547671283752039263)
          ·
            refine ⟨19019021321506925628058895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12679347547671283752039263 19019021321506925628058895)
            ·
              refine ⟨28528531982260388442088343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19019021321506925628058895 28528531982260388442088343)
              ·
                refine ⟨42792797973390582663132515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28528531982260388442088343 42792797973390582663132515)
                ·
                  refine ⟨64189196960085873994698773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42792797973390582663132515 64189196960085873994698773)
                  ·
                    refine ⟨3008868607504025343501505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64189196960085873994698773 3008868607504025343501505)
                    ·
                      refine ⟨2256651455628019007626129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3008868607504025343501505 2256651455628019007626129)
                      ·
                        rfl

theorem cell23_4394813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4394813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394813 prefixEnd_4394813 := by exact prefixLift 4394813
  have htrace : WordTrace (prefixWord ++ tailWord_4394813) baseStart_4394813 baseEnd_4394813 := by
    simpa [prefixWord, tailWord_4394813, baseEnd_4394813] using wordTrace_append hprefix tailTrace_4394813
  have hstable : (prefixWord ++ tailWord_4394813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394813).length < 2 ^ (prefixWord ++ tailWord_4394813).sum := by decide
  have hdescent : baseEnd_4394813 < baseStart_4394813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394833 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_4394833 : Nat := 118140960795 + 4394833 * 2 ^ 59
def prefixEnd_4394833 : Nat := 4983230072969 + 3 ^ 40 * 4394833 * 2
def baseEnd_4394833 : Nat := 2256661725241108929376037

theorem tailTrace_4394833 : CollatzResearch.WordTrace tailWord_4394833 prefixEnd_4394833 2256661725241108929376037 := by
  unfold tailWord_4394833
  simp only [CollatzResearch.WordTrace]
  refine ⟨160292728087278093564965153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106861818724852062376643435 160292728087278093564965153)
  ·
    refine ⟨120219546065458570173723865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160292728087278093564965153 120219546065458570173723865)
    ·
      refine ⟨90164659549093927630292899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120219546065458570173723865 90164659549093927630292899)
      ·
        refine ⟨135246989323640891445439349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90164659549093927630292899 135246989323640891445439349)
        ·
          refine ⟨12679405249091333573009939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135246989323640891445439349 12679405249091333573009939)
          ·
            refine ⟨19019107873637000359514909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12679405249091333573009939 19019107873637000359514909)
            ·
              refine ⟨7132165452613875134818091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19019107873637000359514909 7132165452613875134818091)
              ·
                refine ⟨10698248178920812702227137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7132165452613875134818091 10698248178920812702227137)
                ·
                  refine ⟨8023686134190609526670353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10698248178920812702227137 8023686134190609526670353)
                  ·
                    refine ⟨6017764600642957145002765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8023686134190609526670353 6017764600642957145002765)
                    ·
                      refine ⟨2256661725241108929376037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6017764600642957145002765 2256661725241108929376037)
                      ·
                        rfl

theorem cell23_4394833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_4394833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394833 prefixEnd_4394833 := by exact prefixLift 4394833
  have htrace : WordTrace (prefixWord ++ tailWord_4394833) baseStart_4394833 baseEnd_4394833 := by
    simpa [prefixWord, tailWord_4394833, baseEnd_4394833] using wordTrace_append hprefix tailTrace_4394833
  have hstable : (prefixWord ++ tailWord_4394833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394833).length < 2 ^ (prefixWord ++ tailWord_4394833).sum := by decide
  have hdescent : baseEnd_4394833 < baseStart_4394833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394883 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 1, 5]
def baseStart_4394883 : Nat := 118140960795 + 4394883 * 2 ^ 59
def prefixEnd_4394883 : Nat := 4983230072969 + 3 ^ 40 * 4394883 * 2
def baseEnd_4394883 : Nat := 752229133091277911250269

theorem tailTrace_4394883 : CollatzResearch.WordTrace tailWord_4394883 prefixEnd_4394883 752229133091277911250269 := by
  unfold tailWord_4394883
  simp only [CollatzResearch.WordTrace]
  refine ⟨160294551737096952104285303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106863034491397968069523535 160294551737096952104285303)
  ·
    refine ⟨240441827605645428156427955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160294551737096952104285303 240441827605645428156427955)
    ·
      refine ⟨360662741408468142234641933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240441827605645428156427955 360662741408468142234641933)
      ·
        refine ⟨135248528028175553337990725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360662741408468142234641933 135248528028175553337990725)
        ·
          refine ⟨25359099005282916250873261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135248528028175553337990725 25359099005282916250873261)
          ·
            refine ⟨9509662126981093594077473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25359099005282916250873261 9509662126981093594077473)
            ·
              refine ⟨7132246595235820195558105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9509662126981093594077473 7132246595235820195558105)
              ·
                refine ⟨5349184946426865146668579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7132246595235820195558105 5349184946426865146668579)
                ·
                  refine ⟨8023777419640297720002869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5349184946426865146668579 8023777419640297720002869)
                  ·
                    refine ⟨752229133091277911250269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8023777419640297720002869 752229133091277911250269)
                    ·
                      rfl

theorem cell23_4394883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 5].length) (baseStart_4394883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394883 prefixEnd_4394883 := by exact prefixLift 4394883
  have htrace : WordTrace (prefixWord ++ tailWord_4394883) baseStart_4394883 baseEnd_4394883 := by
    simpa [prefixWord, tailWord_4394883, baseEnd_4394883] using wordTrace_append hprefix tailTrace_4394883
  have hstable : (prefixWord ++ tailWord_4394883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394883).length < 2 ^ (prefixWord ++ tailWord_4394883).sum := by decide
  have hdescent : baseEnd_4394883 < baseStart_4394883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394896 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 4, 4]
def baseStart_4394896 : Nat := 118140960795 + 4394896 * 2 ^ 59
def prefixEnd_4394896 : Nat := 4983230072969 + 3 ^ 40 * 4394896 * 2
def baseEnd_4394896 : Nat := 752231358174114060962749

theorem tailTrace_4394896 : CollatzResearch.WordTrace tailWord_4394896 prefixEnd_4394896 752231358174114060962749 := by
  unfold tailWord_4394896
  simp only [CollatzResearch.WordTrace]
  refine ⟨80147512943024927662254271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106863350590699903549672361 80147512943024927662254271)
  ·
    refine ⟨120221269414537391493381407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80147512943024927662254271 120221269414537391493381407)
    ·
      refine ⟨180331904121806087240072111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120221269414537391493381407 180331904121806087240072111)
      ·
        refine ⟨270497856182709130860108167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180331904121806087240072111 270497856182709130860108167)
        ·
          refine ⟨405746784274063696290162251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270497856182709130860108167 405746784274063696290162251)
          ·
            refine ⟨608620176411095544435243377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405746784274063696290162251 608620176411095544435243377)
            ·
              refine ⟨456465132308321658326432533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608620176411095544435243377 456465132308321658326432533)
              ·
                refine ⟨21396803076952577734051525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456465132308321658326432533 21396803076952577734051525)
                ·
                  refine ⟨4011900576928608325134661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21396803076952577734051525 4011900576928608325134661)
                  ·
                    refine ⟨752231358174114060962749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4011900576928608325134661 752231358174114060962749)
                    ·
                      rfl

theorem cell23_4394896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_4394896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394896 prefixEnd_4394896 := by exact prefixLift 4394896
  have htrace : WordTrace (prefixWord ++ tailWord_4394896) baseStart_4394896 baseEnd_4394896 := by
    simpa [prefixWord, tailWord_4394896, baseEnd_4394896] using wordTrace_append hprefix tailTrace_4394896
  have hstable : (prefixWord ++ tailWord_4394896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394896).length < 2 ^ (prefixWord ++ tailWord_4394896).sum := by decide
  have hdescent : baseEnd_4394896 < baseStart_4394896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394903 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_4394903 : Nat := 118140960795 + 4394903 * 2 ^ 59
def prefixEnd_4394903 : Nat := 4983230072969 + 3 ^ 40 * 4394903 * 2
def baseEnd_4394903 : Nat := 2256697668886923655500715

theorem tailTrace_4394903 : CollatzResearch.WordTrace tailWord_4394903 prefixEnd_4394903 2256697668886923655500715 := by
  unfold tailWord_4394903
  simp only [CollatzResearch.WordTrace]
  refine ⟨160295281197024495520013363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106863520798016330346675575 160295281197024495520013363)
  ·
    refine ⟨240442921795536743280020045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160295281197024495520013363 240442921795536743280020045)
    ·
      refine ⟨90166095673326278730007517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240442921795536743280020045 90166095673326278730007517)
      ·
        refine ⟨33812285877497354523752819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90166095673326278730007517 33812285877497354523752819)
        ·
          refine ⟨50718428816246031785629229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33812285877497354523752819 50718428816246031785629229)
          ·
            refine ⟨19019410806092261919610961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50718428816246031785629229 19019410806092261919610961)
            ·
              refine ⟨14264558104569196439708221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19019410806092261919610961 14264558104569196439708221)
              ·
                refine ⟨5349209289213448664890583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14264558104569196439708221 5349209289213448664890583)
                ·
                  refine ⟨8023813933820172997335875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5349209289213448664890583 8023813933820172997335875)
                  ·
                    refine ⟨12035720900730259496003813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8023813933820172997335875 12035720900730259496003813)
                    ·
                      refine ⟨2256697668886923655500715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12035720900730259496003813 2256697668886923655500715)
                      ·
                        rfl

theorem cell23_4394903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_4394903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394903 prefixEnd_4394903 := by exact prefixLift 4394903
  have htrace : WordTrace (prefixWord ++ tailWord_4394903) baseStart_4394903 baseEnd_4394903 := by
    simpa [prefixWord, tailWord_4394903, baseEnd_4394903] using wordTrace_append hprefix tailTrace_4394903
  have hstable : (prefixWord ++ tailWord_4394903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394903).length < 2 ^ (prefixWord ++ tailWord_4394903).sum := by decide
  have hdescent : baseEnd_4394903 < baseStart_4394903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394914 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_4394914 : Nat := 118140960795 + 4394914 * 2 ^ 59
def prefixEnd_4394914 : Nat := 4983230072969 + 3 ^ 40 * 4394914 * 2
def baseEnd_4394914 : Nat := 2256703317174123112463165

theorem tailTrace_4394914 : CollatzResearch.WordTrace tailWord_4394914 prefixEnd_4394914 2256703317174123112463165 := by
  unfold tailWord_4394914
  simp only [CollatzResearch.WordTrace]
  refine ⟨40073920599996161099665949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106863788266656429599109197 40073920599996161099665949)
  ·
    refine ⟨15027720224998560412374731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40073920599996161099665949 15027720224998560412374731)
    ·
      refine ⟨22541580337497840618562097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15027720224998560412374731 22541580337497840618562097)
      ·
        refine ⟨16906185253123380463921573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22541580337497840618562097 16906185253123380463921573)
        ·
          refine ⟨3169909734960633836985295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16906185253123380463921573 3169909734960633836985295)
          ·
            refine ⟨4754864602440950755477943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169909734960633836985295 4754864602440950755477943)
            ·
              refine ⟨7132296903661426133216915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754864602440950755477943 7132296903661426133216915)
              ·
                refine ⟨10698445355492139199825373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7132296903661426133216915 10698445355492139199825373)
                ·
                  refine ⟨4011917008309552199934515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10698445355492139199825373 4011917008309552199934515)
                  ·
                    refine ⟨6017875512464328299901773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4011917008309552199934515 6017875512464328299901773)
                    ·
                      refine ⟨2256703317174123112463165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6017875512464328299901773 2256703317174123112463165)
                      ·
                        rfl

theorem cell23_4394914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_4394914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394914 prefixEnd_4394914 := by exact prefixLift 4394914
  have htrace : WordTrace (prefixWord ++ tailWord_4394914) baseStart_4394914 baseEnd_4394914 := by
    simpa [prefixWord, tailWord_4394914, baseEnd_4394914] using wordTrace_append hprefix tailTrace_4394914
  have hstable : (prefixWord ++ tailWord_4394914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394914).length < 2 ^ (prefixWord ++ tailWord_4394914).sum := by decide
  have hdescent : baseEnd_4394914 < baseStart_4394914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4394916 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_4394916 : Nat := 118140960795 + 4394916 * 2 ^ 59
def prefixEnd_4394916 : Nat := 4983230072969 + 3 ^ 40 * 4394916 * 2
def baseEnd_4394916 : Nat := 2256704344135432104638155

theorem tailTrace_4394916 : CollatzResearch.WordTrace tailWord_4394916 prefixEnd_4394916 2256704344135432104638155 := by
  unfold tailWord_4394916
  simp only [CollatzResearch.WordTrace]
  refine ⟨80147877672988699370118301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106863836897318265826824401 80147877672988699370118301)
  ·
    refine ⟨30055454127370762263794363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80147877672988699370118301 30055454127370762263794363)
    ·
      refine ⟨45083181191056143395691545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30055454127370762263794363 45083181191056143395691545)
      ·
        refine ⟨33812385893292107546768659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45083181191056143395691545 33812385893292107546768659)
        ·
          refine ⟨50718578839938161320152989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33812385893292107546768659 50718578839938161320152989)
          ·
            refine ⟨19019467064976810495057371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50718578839938161320152989 19019467064976810495057371)
            ·
              refine ⟨28529200597465215742586057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19019467064976810495057371 28529200597465215742586057)
              ·
                refine ⟨21396900448098911806939543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28529200597465215742586057 21396900448098911806939543)
                ·
                  refine ⟨32095350672148367710409315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21396900448098911806939543 32095350672148367710409315)
                  ·
                    refine ⟨48143026008222551565613973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32095350672148367710409315 48143026008222551565613973)
                    ·
                      refine ⟨2256704344135432104638155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48143026008222551565613973 2256704344135432104638155)
                      ·
                        rfl

theorem cell23_4394916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_4394916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4394916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4394916 prefixEnd_4394916 := by exact prefixLift 4394916
  have htrace : WordTrace (prefixWord ++ tailWord_4394916) baseStart_4394916 baseEnd_4394916 := by
    simpa [prefixWord, tailWord_4394916, baseEnd_4394916] using wordTrace_append hprefix tailTrace_4394916
  have hstable : (prefixWord ++ tailWord_4394916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4394916).length < 2 ^ (prefixWord ++ tailWord_4394916).sum := by decide
  have hdescent : baseEnd_4394916 < baseStart_4394916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4394916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395016 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 9]
def baseStart_4395016 : Nat := 118140960795 + 4395016 * 2 ^ 59
def prefixEnd_4395016 : Nat := 4983230072969 + 3 ^ 40 * 4395016 * 2
def baseEnd_4395016 : Nat := 250750632466764634820855

theorem tailTrace_4395016 : CollatzResearch.WordTrace tailWord_4395016 prefixEnd_4395016 250750632466764634820855 := by
  unfold tailWord_4395016
  simp only [CollatzResearch.WordTrace]
  refine ⟨80149701322807557909438451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106866268430410077212584601 80149701322807557909438451)
  ·
    refine ⟨120224551984211336864157677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80149701322807557909438451 120224551984211336864157677)
    ·
      refine ⟨45084206994079251324059129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120224551984211336864157677 45084206994079251324059129)
      ·
        refine ⟨33813155245559438493044347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45084206994079251324059129 33813155245559438493044347)
        ·
          refine ⟨50719732868339157739566521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33813155245559438493044347 50719732868339157739566521)
          ·
            refine ⟨38039799651254368304674891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50719732868339157739566521 38039799651254368304674891)
            ·
              refine ⟨57059699476881552457012337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38039799651254368304674891 57059699476881552457012337)
              ·
                refine ⟨42794774607661164342759253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57059699476881552457012337 42794774607661164342759253)
                ·
                  refine ⟨250750632466764634820855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42794774607661164342759253 250750632466764634820855)
                  ·
                    rfl

theorem cell23_4395016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 9].length) (baseStart_4395016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395016 prefixEnd_4395016 := by exact prefixLift 4395016
  have htrace : WordTrace (prefixWord ++ tailWord_4395016) baseStart_4395016 baseEnd_4395016 := by
    simpa [prefixWord, tailWord_4395016, baseEnd_4395016] using wordTrace_append hprefix tailTrace_4395016
  have hstable : (prefixWord ++ tailWord_4395016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395016).length < 2 ^ (prefixWord ++ tailWord_4395016).sum := by decide
  have hdescent : baseEnd_4395016 < baseStart_4395016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395021 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4395021 : Nat := 118140960795 + 4395021 * 2 ^ 59
def prefixEnd_4395021 : Nat := 4983230072969 + 3 ^ 40 * 4395021 * 2
def baseEnd_4395021 : Nat := 2256758259604154193825173

theorem tailTrace_4395021 : CollatzResearch.WordTrace tailWord_4395021 prefixEnd_4395021 2256758259604154193825173 := by
  unfold tailWord_4395021
  simp only [CollatzResearch.WordTrace]
  refine ⟨160299585010597001672808917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106866390007064667781872611 160299585010597001672808917)
  ·
    refine ⟨3757021523685867226706459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 160299585010597001672808917 3757021523685867226706459)
    ·
      refine ⟨5635532285528800840059689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757021523685867226706459 5635532285528800840059689)
      ·
        refine ⟨4226649214146600630044767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5635532285528800840059689 4226649214146600630044767)
        ·
          refine ⟨6339973821219900945067151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4226649214146600630044767 6339973821219900945067151)
          ·
            refine ⟨9509960731829851417600727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6339973821219900945067151 9509960731829851417600727)
            ·
              refine ⟨14264941097744777126401091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9509960731829851417600727 14264941097744777126401091)
              ·
                refine ⟨21397411646617165689601637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14264941097744777126401091 21397411646617165689601637)
                ·
                  refine ⟨4012014683740718566800307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21397411646617165689601637 4012014683740718566800307)
                  ·
                    refine ⟨6018022025611077850200461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012014683740718566800307 6018022025611077850200461)
                    ·
                      refine ⟨2256758259604154193825173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018022025611077850200461 2256758259604154193825173)
                      ·
                        rfl

theorem cell23_4395021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4395021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395021 prefixEnd_4395021 := by exact prefixLift 4395021
  have htrace : WordTrace (prefixWord ++ tailWord_4395021) baseStart_4395021 baseEnd_4395021 := by
    simpa [prefixWord, tailWord_4395021, baseEnd_4395021] using wordTrace_append hprefix tailTrace_4395021
  have hstable : (prefixWord ++ tailWord_4395021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395021).length < 2 ^ (prefixWord ++ tailWord_4395021).sum := by decide
  have hdescent : baseEnd_4395021 < baseStart_4395021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395027 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 2, 2, 2]
def baseStart_4395027 : Nat := 118140960795 + 4395027 * 2 ^ 59
def prefixEnd_4395027 : Nat := 4983230072969 + 3 ^ 40 * 4395027 * 2
def baseEnd_4395027 : Nat := 2256761340488081170350145

theorem tailTrace_4395027 : CollatzResearch.WordTrace tailWord_4395027 prefixEnd_4395027 2256761340488081170350145 := by
  unfold tailWord_4395027
  simp only [CollatzResearch.WordTrace]
  refine ⟨160299803848575264697527335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106866535899050176465018223 160299803848575264697527335)
  ·
    refine ⟨240449705772862897046291003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160299803848575264697527335 240449705772862897046291003)
    ·
      refine ⟨360674558659294345569436505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240449705772862897046291003 360674558659294345569436505)
      ·
        refine ⟨270505918994470759177077379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360674558659294345569436505 270505918994470759177077379)
        ·
          refine ⟨405758878491706138765616069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270505918994470759177077379 405758878491706138765616069)
          ·
            refine ⟨76079789717194901018553013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 405758878491706138765616069 76079789717194901018553013)
            ·
              refine ⟨7132480285987021970489345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76079789717194901018553013 7132480285987021970489345)
              ·
                refine ⟨5349360214490266477867009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7132480285987021970489345 5349360214490266477867009)
                ·
                  refine ⟨4012020160867699858400257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5349360214490266477867009 4012020160867699858400257)
                  ·
                    refine ⟨3009015120650774893800193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4012020160867699858400257 3009015120650774893800193)
                    ·
                      refine ⟨2256761340488081170350145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009015120650774893800193 2256761340488081170350145)
                      ·
                        rfl

theorem cell23_4395027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 2, 2].length) (baseStart_4395027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395027 prefixEnd_4395027 := by exact prefixLift 4395027
  have htrace : WordTrace (prefixWord ++ tailWord_4395027) baseStart_4395027 baseEnd_4395027 := by
    simpa [prefixWord, tailWord_4395027, baseEnd_4395027] using wordTrace_append hprefix tailTrace_4395027
  have hstable : (prefixWord ++ tailWord_4395027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395027).length < 2 ^ (prefixWord ++ tailWord_4395027).sum := by decide
  have hdescent : baseEnd_4395027 < baseStart_4395027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395043 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 3]
def baseStart_4395043 : Nat := 118140960795 + 4395043 * 2 ^ 59
def prefixEnd_4395043 : Nat := 4983230072969 + 3 ^ 40 * 4395043 * 2
def baseEnd_4395043 : Nat := 2256769556178553107750071

theorem tailTrace_4395043 : CollatzResearch.WordTrace tailWord_4395043 prefixEnd_4395043 2256769556178553107750071 := by
  unfold tailWord_4395043
  simp only [CollatzResearch.WordTrace]
  refine ⟨160300387416517299430109783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106866924944344866286739855 160300387416517299430109783)
  ·
    refine ⟨240450581124775949145164675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160300387416517299430109783 240450581124775949145164675)
    ·
      refine ⟨360675871687163923717747013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240450581124775949145164675 360675871687163923717747013)
      ·
        refine ⟨67626725941343235697077565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360675871687163923717747013 67626725941343235697077565)
        ·
          refine ⟨25360022228003713386404087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67626725941343235697077565 25360022228003713386404087)
          ·
            refine ⟨38040033342005570079606131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25360022228003713386404087 38040033342005570079606131)
            ·
              refine ⟨57060050013008355119409197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38040033342005570079606131 57060050013008355119409197)
              ·
                refine ⟨21397518754878133169778449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57060050013008355119409197 21397518754878133169778449)
                ·
                  refine ⟨16048139066158599877333837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21397518754878133169778449 16048139066158599877333837)
                  ·
                    refine ⟨6018052149809474954000189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16048139066158599877333837 6018052149809474954000189)
                    ·
                      refine ⟨2256769556178553107750071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018052149809474954000189 2256769556178553107750071)
                      ·
                        rfl

theorem cell23_4395043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_4395043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395043 prefixEnd_4395043 := by exact prefixLift 4395043
  have htrace : WordTrace (prefixWord ++ tailWord_4395043) baseStart_4395043 baseEnd_4395043 := by
    simpa [prefixWord, tailWord_4395043, baseEnd_4395043] using wordTrace_append hprefix tailTrace_4395043
  have hstable : (prefixWord ++ tailWord_4395043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395043).length < 2 ^ (prefixWord ++ tailWord_4395043).sum := by decide
  have hdescent : baseEnd_4395043 < baseStart_4395043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395044 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_4395044 : Nat := 118140960795 + 4395044 * 2 ^ 59
def prefixEnd_4395044 : Nat := 4983230072969 + 3 ^ 40 * 4395044 * 2
def baseEnd_4395044 : Nat := 2256770069659207603837567

theorem tailTrace_4395044 : CollatzResearch.WordTrace tailWord_4395044 prefixEnd_4395044 2256770069659207603837567 := by
  unfold tailWord_4395044
  simp only [CollatzResearch.WordTrace]
  refine ⟨80150211944756838300448093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106866949259675784400597457 80150211944756838300448093)
  ·
    refine ⟨30056329479283814362668035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80150211944756838300448093 30056329479283814362668035)
    ·
      refine ⟨45084494218925721544002053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30056329479283814362668035 45084494218925721544002053)
      ·
        refine ⟨8453342666048572789500385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45084494218925721544002053 8453342666048572789500385)
        ·
          refine ⟨6340006999536429592125289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8453342666048572789500385 6340006999536429592125289)
          ·
            refine ⟨4755005249652322194093967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6340006999536429592125289 4755005249652322194093967)
            ·
              refine ⟨7132507874478483291140951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755005249652322194093967 7132507874478483291140951)
              ·
                refine ⟨10698761811717724936711427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7132507874478483291140951 10698761811717724936711427)
                ·
                  refine ⟨16048142717576587405067141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10698761811717724936711427 16048142717576587405067141)
                  ·
                    refine ⟨3009026759545610138450089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16048142717576587405067141 3009026759545610138450089)
                    ·
                      refine ⟨2256770069659207603837567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009026759545610138450089 2256770069659207603837567)
                      ·
                        rfl

theorem cell23_4395044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_4395044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395044 prefixEnd_4395044 := by exact prefixLift 4395044
  have htrace : WordTrace (prefixWord ++ tailWord_4395044) baseStart_4395044 baseEnd_4395044 := by
    simpa [prefixWord, tailWord_4395044, baseEnd_4395044] using wordTrace_append hprefix tailTrace_4395044
  have hstable : (prefixWord ++ tailWord_4395044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395044).length < 2 ^ (prefixWord ++ tailWord_4395044).sum := by decide
  have hdescent : baseEnd_4395044 < baseStart_4395044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395083 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 4]
def baseStart_4395083 : Nat := 118140960795 + 4395083 * 2 ^ 59
def prefixEnd_4395083 : Nat := 4983230072969 + 3 ^ 40 * 4395083 * 2
def baseEnd_4395083 : Nat := 2256790095404732951249887

theorem tailTrace_4395083 : CollatzResearch.WordTrace tailWord_4395083 prefixEnd_4395083 2256790095404732951249887 := by
  unfold tailWord_4395083
  simp only [CollatzResearch.WordTrace]
  refine ⟨160301846336372386261565903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106867897557581590841043935 160301846336372386261565903)
  ·
    refine ⟨240452769504558579392348855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160301846336372386261565903 240452769504558579392348855)
    ·
      refine ⟨360679154256837869088523283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240452769504558579392348855 360679154256837869088523283)
      ·
        refine ⟨541018731385256803632784925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360679154256837869088523283 541018731385256803632784925)
        ·
          refine ⟨202882024269471301362294347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 541018731385256803632784925 202882024269471301362294347)
          ·
            refine ⟨304323036404206952043441521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202882024269471301362294347 304323036404206952043441521)
            ·
              refine ⟨228242277303155214032581141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304323036404206952043441521 228242277303155214032581141)
              ·
                refine ⟨10698856748585400657777241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228242277303155214032581141 10698856748585400657777241)
                ·
                  refine ⟨8024142561439050493332931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10698856748585400657777241 8024142561439050493332931)
                  ·
                    refine ⟨12036213842158575739999397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8024142561439050493332931 12036213842158575739999397)
                    ·
                      refine ⟨2256790095404732951249887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12036213842158575739999397 2256790095404732951249887)
                      ·
                        rfl

theorem cell23_4395083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 4].length) (baseStart_4395083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395083 prefixEnd_4395083 := by exact prefixLift 4395083
  have htrace : WordTrace (prefixWord ++ tailWord_4395083) baseStart_4395083 baseEnd_4395083 := by
    simpa [prefixWord, tailWord_4395083, baseEnd_4395083] using wordTrace_append hprefix tailTrace_4395083
  have hstable : (prefixWord ++ tailWord_4395083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395083).length < 2 ^ (prefixWord ++ tailWord_4395083).sum := by decide
  have hdescent : baseEnd_4395083 < baseStart_4395083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395090 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_4395090 : Nat := 118140960795 + 4395090 * 2 ^ 59
def prefixEnd_4395090 : Nat := 4983230072969 + 3 ^ 40 * 4395090 * 2
def baseEnd_4395090 : Nat := 2256793689769314423862355

theorem tailTrace_4395090 : CollatzResearch.WordTrace tailWord_4395090 prefixEnd_4395090 2256793689769314423862355 := by
  unfold tailWord_4395090
  simp only [CollatzResearch.WordTrace]
  refine ⟨40075525411836756614267681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106868067764898017638047149 40075525411836756614267681)
  ·
    refine ⟨30056644058877567460700761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40075525411836756614267681 30056644058877567460700761)
    ·
      refine ⟨22542483044158175595525571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30056644058877567460700761 22542483044158175595525571)
      ·
        refine ⟨33813724566237263393288357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22542483044158175595525571 33813724566237263393288357)
        ·
          refine ⟨6340073356169486886241567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33813724566237263393288357 6340073356169486886241567)
          ·
            refine ⟨9510110034254230329362351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6340073356169486886241567 9510110034254230329362351)
            ·
              refine ⟨14265165051381345494043527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9510110034254230329362351 14265165051381345494043527)
              ·
                refine ⟨21397747577072018241065291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14265165051381345494043527 21397747577072018241065291)
                ·
                  refine ⟨32096621365608027361597937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21397747577072018241065291 32096621365608027361597937)
                  ·
                    refine ⟨24072466024206020521198453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32096621365608027361597937 24072466024206020521198453)
                    ·
                      refine ⟨2256793689769314423862355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24072466024206020521198453 2256793689769314423862355)
                      ·
                        rfl

theorem cell23_4395090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_4395090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395090 prefixEnd_4395090 := by exact prefixLift 4395090
  have htrace : WordTrace (prefixWord ++ tailWord_4395090) baseStart_4395090 baseEnd_4395090 := by
    simpa [prefixWord, tailWord_4395090, baseEnd_4395090] using wordTrace_append hprefix tailTrace_4395090
  have hstable : (prefixWord ++ tailWord_4395090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395090).length < 2 ^ (prefixWord ++ tailWord_4395090).sum := by decide
  have hdescent : baseEnd_4395090 < baseStart_4395090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395103 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 3]
def baseStart_4395103 : Nat := 118140960795 + 4395103 * 2 ^ 59
def prefixEnd_4395103 : Nat := 4983230072969 + 3 ^ 40 * 4395103 * 2
def baseEnd_4395103 : Nat := 2256800365017822872999795

theorem tailTrace_4395103 : CollatzResearch.WordTrace tailWord_4395103 prefixEnd_4395103 2256800365017822872999795 := by
  unfold tailWord_4395103
  simp only [CollatzResearch.WordTrace]
  refine ⟨160302575796299929677293963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106868383864199953118195975 160302575796299929677293963)
  ·
    refine ⟨240453863694449894515940945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160302575796299929677293963 240453863694449894515940945)
    ·
      refine ⟨180340397770837420886955709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240453863694449894515940945 180340397770837420886955709)
      ·
        refine ⟨67627649164064032832608391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180340397770837420886955709 67627649164064032832608391)
        ·
          refine ⟨101441473746096049248912587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67627649164064032832608391 101441473746096049248912587)
          ·
            refine ⟨152162210619144073873368881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101441473746096049248912587 152162210619144073873368881)
            ·
              refine ⟨114121657964358055405026661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152162210619144073873368881 114121657964358055405026661)
              ·
                refine ⟨21397810868317135388442499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114121657964358055405026661 21397810868317135388442499)
                ·
                  refine ⟨32096716302475703082663749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21397810868317135388442499 32096716302475703082663749)
                  ·
                    refine ⟨6018134306714194327999453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32096716302475703082663749 6018134306714194327999453)
                    ·
                      refine ⟨2256800365017822872999795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018134306714194327999453 2256800365017822872999795)
                      ·
                        rfl

theorem cell23_4395103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_4395103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395103 prefixEnd_4395103 := by exact prefixLift 4395103
  have htrace : WordTrace (prefixWord ++ tailWord_4395103) baseStart_4395103 baseEnd_4395103 := by
    simpa [prefixWord, tailWord_4395103, baseEnd_4395103] using wordTrace_append hprefix tailTrace_4395103
  have hstable : (prefixWord ++ tailWord_4395103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395103).length < 2 ^ (prefixWord ++ tailWord_4395103).sum := by decide
  have hdescent : baseEnd_4395103 < baseStart_4395103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395120 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3]
def baseStart_4395120 : Nat := 118140960795 + 4395120 * 2 ^ 59
def prefixEnd_4395120 : Nat := 4983230072969 + 3 ^ 40 * 4395120 * 2
def baseEnd_4395120 : Nat := 2256809094188949306487217

theorem tailTrace_4395120 : CollatzResearch.WordTrace tailWord_4395120 prefixEnd_4395120 2256809094188949306487217 := by
  unfold tailWord_4395120
  simp only [CollatzResearch.WordTrace]
  refine ⟨80151597918619170790331407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106868797224825561053775209 80151597918619170790331407)
  ·
    refine ⟨120227396877928756185497111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80151597918619170790331407 120227396877928756185497111)
    ·
      refine ⟨180341095316893134278245667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120227396877928756185497111 180341095316893134278245667)
      ·
        refine ⟨270511642975339701417368501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180341095316893134278245667 270511642975339701417368501)
        ·
          refine ⟨25360466528938097007878297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 270511642975339701417368501 25360466528938097007878297)
          ·
            refine ⟨19020349896703572755908723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25360466528938097007878297 19020349896703572755908723)
            ·
              refine ⟨28530524845055359133863085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19020349896703572755908723 28530524845055359133863085)
              ·
                refine ⟨10698946816895759675198657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28530524845055359133863085 10698946816895759675198657)
                ·
                  refine ⟨8024210112671819756398993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10698946816895759675198657 8024210112671819756398993)
                  ·
                    refine ⟨6018157584503864817299245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8024210112671819756398993 6018157584503864817299245)
                    ·
                      refine ⟨2256809094188949306487217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018157584503864817299245 2256809094188949306487217)
                      ·
                        rfl

theorem cell23_4395120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_4395120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395120 prefixEnd_4395120 := by exact prefixLift 4395120
  have htrace : WordTrace (prefixWord ++ tailWord_4395120) baseStart_4395120 baseEnd_4395120 := by
    simpa [prefixWord, tailWord_4395120, baseEnd_4395120] using wordTrace_append hprefix tailTrace_4395120
  have hstable : (prefixWord ++ tailWord_4395120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395120).length < 2 ^ (prefixWord ++ tailWord_4395120).sum := by decide
  have hdescent : baseEnd_4395120 < baseStart_4395120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395140 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 6]
def baseStart_4395140 : Nat := 118140960795 + 4395140 * 2 ^ 59
def prefixEnd_4395140 : Nat := 4983230072969 + 3 ^ 40 * 4395140 * 2
def baseEnd_4395140 : Nat := 250757707089115469804125

theorem tailTrace_4395140 : CollatzResearch.WordTrace tailWord_4395140 prefixEnd_4395140 250757707089115469804125 := by
  unfold tailWord_4395140
  simp only [CollatzResearch.WordTrace]
  refine ⟨80151962648582942498195437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106869283531443923330927249 80151962648582942498195437)
  ·
    refine ⟨30056985993218603436823289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80151962648582942498195437 30056985993218603436823289)
    ·
      refine ⟨22542739494913952577617467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30056985993218603436823289 22542739494913952577617467)
      ·
        refine ⟨33814109242370928866426201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22542739494913952577617467 33814109242370928866426201)
        ·
          refine ⟨25360581931778196649819651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33814109242370928866426201 25360581931778196649819651)
          ·
            refine ⟨38040872897667294974729477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25360581931778196649819651 38040872897667294974729477)
            ·
              refine ⟨7132663668312617807761777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38040872897667294974729477 7132663668312617807761777)
              ·
                refine ⟨5349497751234463355821333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7132663668312617807761777 5349497751234463355821333)
                ·
                  refine ⟨250757707089115469804125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5349497751234463355821333 250757707089115469804125)
                  ·
                    rfl

theorem cell23_4395140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_4395140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395140 prefixEnd_4395140 := by exact prefixLift 4395140
  have htrace : WordTrace (prefixWord ++ tailWord_4395140) baseStart_4395140 baseEnd_4395140 := by
    simpa [prefixWord, tailWord_4395140, baseEnd_4395140] using wordTrace_append hprefix tailTrace_4395140
  have hstable : (prefixWord ++ tailWord_4395140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395140).length < 2 ^ (prefixWord ++ tailWord_4395140).sum := by decide
  have hdescent : baseEnd_4395140 < baseStart_4395140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395144 : List Nat := [2, 1, 3, 4, 1, 2, 1, 4, 1, 4]
def baseStart_4395144 : Nat := 118140960795 + 4395144 * 2 ^ 59
def prefixEnd_4395144 : Nat := 4983230072969 + 3 ^ 40 * 4395144 * 2
def baseEnd_4395144 : Nat := 752273805908219070862369

theorem tailTrace_4395144 : CollatzResearch.WordTrace tailWord_4395144 prefixEnd_4395144 752273805908219070862369 := by
  unfold tailWord_4395144
  simp only [CollatzResearch.WordTrace]
  refine ⟨80152035594575696839768243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106869380792767595786357657 80152035594575696839768243)
  ·
    refine ⟨120228053391863545259652365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80152035594575696839768243 120228053391863545259652365)
    ·
      refine ⟨45085520021948829472369637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120228053391863545259652365 45085520021948829472369637)
      ·
        refine ⟨8453535004115405526069307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45085520021948829472369637 8453535004115405526069307)
        ·
          refine ⟨12680302506173108289103961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8453535004115405526069307 12680302506173108289103961)
          ·
            refine ⟨9510226879629831216827971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12680302506173108289103961 9510226879629831216827971)
            ·
              refine ⟨14265340319444746825241957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9510226879629831216827971 14265340319444746825241957)
              ·
                refine ⟨2674751309895890029732867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14265340319444746825241957 2674751309895890029732867)
                ·
                  refine ⟨4012126964843835044599301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674751309895890029732867 4012126964843835044599301)
                  ·
                    refine ⟨752273805908219070862369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012126964843835044599301 752273805908219070862369)
                    ·
                      rfl

theorem cell23_4395144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_4395144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395144 prefixEnd_4395144 := by exact prefixLift 4395144
  have htrace : WordTrace (prefixWord ++ tailWord_4395144) baseStart_4395144 baseEnd_4395144 := by
    simpa [prefixWord, tailWord_4395144, baseEnd_4395144] using wordTrace_append hprefix tailTrace_4395144
  have hstable : (prefixWord ++ tailWord_4395144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395144).length < 2 ^ (prefixWord ++ tailWord_4395144).sum := by decide
  have hdescent : baseEnd_4395144 < baseStart_4395144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395167 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4395167 : Nat := 118140960795 + 4395167 * 2 ^ 59
def prefixEnd_4395167 : Nat := 4983230072969 + 3 ^ 40 * 4395167 * 2
def baseEnd_4395167 : Nat := 2256833227779710622599501

theorem tailTrace_4395167 : CollatzResearch.WordTrace tailWord_4395167 prefixEnd_4395167 2256833227779710622599501 := by
  unfold tailWord_4395167
  simp only [CollatzResearch.WordTrace]
  refine ⟨160304910068068068607623755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106869940045378712405082503 160304910068068068607623755)
  ·
    refine ⟨240457365102102102911435633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160304910068068068607623755 240457365102102102911435633)
    ·
      refine ⟨180343023826576577183576725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240457365102102102911435633 180343023826576577183576725)
      ·
        refine ⟨8453579241870777055480159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180343023826576577183576725 8453579241870777055480159)
        ·
          refine ⟨12680368862806165583220239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8453579241870777055480159 12680368862806165583220239)
          ·
            refine ⟨19020553294209248374830359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12680368862806165583220239 19020553294209248374830359)
            ·
              refine ⟨28530829941313872562245539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19020553294209248374830359 28530829941313872562245539)
              ·
                refine ⟨42796244911970808843368309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28530829941313872562245539 42796244911970808843368309)
                ·
                  refine ⟨4012147960497263329065779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42796244911970808843368309 4012147960497263329065779)
                  ·
                    refine ⟨6018221940745894993598669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012147960497263329065779 6018221940745894993598669)
                    ·
                      refine ⟨2256833227779710622599501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018221940745894993598669 2256833227779710622599501)
                      ·
                        rfl

theorem cell23_4395167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4395167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395167 prefixEnd_4395167 := by exact prefixLift 4395167
  have htrace : WordTrace (prefixWord ++ tailWord_4395167) baseStart_4395167 baseEnd_4395167 := by
    simpa [prefixWord, tailWord_4395167, baseEnd_4395167] using wordTrace_append hprefix tailTrace_4395167
  have hstable : (prefixWord ++ tailWord_4395167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395167).length < 2 ^ (prefixWord ++ tailWord_4395167).sum := by decide
  have hdescent : baseEnd_4395167 < baseStart_4395167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395201 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4395201 : Nat := 118140960795 + 4395201 * 2 ^ 59
def prefixEnd_4395201 : Nat := 4983230072969 + 3 ^ 40 * 4395201 * 2
def baseEnd_4395201 : Nat := 2256850686121963489574345

theorem tailTrace_4395201 : CollatzResearch.WordTrace tailWord_4395201 prefixEnd_4395201 2256850686121963489574345 := by
  unfold tailWord_4395201
  simp only [CollatzResearch.WordTrace]
  refine ⟨160306150149944892414361457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106870766766629928276240971 160306150149944892414361457)
  ·
    refine ⟨120229612612458669310771093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160306150149944892414361457 120229612612458669310771093)
    ·
      refine ⟨5635763091209000123942395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120229612612458669310771093 5635763091209000123942395)
      ·
        refine ⟨8453644636813500185913593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5635763091209000123942395 8453644636813500185913593)
        ·
          refine ⟨6340233477610125139435195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8453644636813500185913593 6340233477610125139435195)
          ·
            refine ⟨9510350216415187709152793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6340233477610125139435195 9510350216415187709152793)
            ·
              refine ⟨7132762662311390781864595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9510350216415187709152793 7132762662311390781864595)
              ·
                refine ⟨10699143993467086172796893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7132762662311390781864595 10699143993467086172796893)
                ·
                  refine ⟨4012178997550157314798835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10699143993467086172796893 4012178997550157314798835)
                  ·
                    refine ⟨6018268496325235972198253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012178997550157314798835 6018268496325235972198253)
                    ·
                      refine ⟨2256850686121963489574345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018268496325235972198253 2256850686121963489574345)
                      ·
                        rfl

theorem cell23_4395201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4395201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395201 prefixEnd_4395201 := by exact prefixLift 4395201
  have htrace : WordTrace (prefixWord ++ tailWord_4395201) baseStart_4395201 baseEnd_4395201 := by
    simpa [prefixWord, tailWord_4395201, baseEnd_4395201] using wordTrace_append hprefix tailTrace_4395201
  have hstable : (prefixWord ++ tailWord_4395201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395201).length < 2 ^ (prefixWord ++ tailWord_4395201).sum := by decide
  have hdescent : baseEnd_4395201 < baseStart_4395201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395210 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_4395210 : Nat := 118140960795 + 4395210 * 2 ^ 59
def prefixEnd_4395210 : Nat := 4983230072969 + 3 ^ 40 * 4395210 * 2
def baseEnd_4395210 : Nat := 2256855307447853954361803

theorem tailTrace_4395210 : CollatzResearch.WordTrace tailWord_4395210 prefixEnd_4395210 2256855307447853954361803 := by
  unfold tailWord_4395210
  simp only [CollatzResearch.WordTrace]
  refine ⟨40076619601728071737859771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106870985604608191300959389 40076619601728071737859771)
  ·
    refine ⟨60114929402592107606789657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40076619601728071737859771 60114929402592107606789657)
    ·
      refine ⟨45086197051944080705092243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60114929402592107606789657 45086197051944080705092243)
      ·
        refine ⟨67629295577916121057638365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45086197051944080705092243 67629295577916121057638365)
        ·
          refine ⟨25360985841718545396614387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67629295577916121057638365 25360985841718545396614387)
          ·
            refine ⟨38041478762577818094921581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25360985841718545396614387 38041478762577818094921581)
            ·
              refine ⟨14265554535966681785595593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38041478762577818094921581 14265554535966681785595593)
              ·
                refine ⟨10699165901975011339196695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14265554535966681785595593 10699165901975011339196695)
                ·
                  refine ⟨16048748852962517008795043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10699165901975011339196695 16048748852962517008795043)
                  ·
                    refine ⟨24073123279443775513192565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16048748852962517008795043 24073123279443775513192565)
                    ·
                      refine ⟨2256855307447853954361803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24073123279443775513192565 2256855307447853954361803)
                      ·
                        rfl

theorem cell23_4395210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_4395210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395210 prefixEnd_4395210 := by exact prefixLift 4395210
  have htrace : WordTrace (prefixWord ++ tailWord_4395210) baseStart_4395210 baseEnd_4395210 := by
    simpa [prefixWord, tailWord_4395210, baseEnd_4395210] using wordTrace_append hprefix tailTrace_4395210
  have hstable : (prefixWord ++ tailWord_4395210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395210).length < 2 ^ (prefixWord ++ tailWord_4395210).sum := by decide
  have hdescent : baseEnd_4395210 < baseStart_4395210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395224 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 3, 2, 2]
def baseStart_4395224 : Nat := 118140960795 + 4395224 * 2 ^ 59
def prefixEnd_4395224 : Nat := 4983230072969 + 3 ^ 40 * 4395224 * 2
def baseEnd_4395224 : Nat := 2256862496177016899586739

theorem tailTrace_4395224 : CollatzResearch.WordTrace tailWord_4395224 prefixEnd_4395224 2256862496177016899586739 := by
  unfold tailWord_4395224
  simp only [CollatzResearch.WordTrace]
  refine ⟨80153494514430783671224363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106871326019241044894965817 80153494514430783671224363)
  ·
    refine ⟨120230241771646175506836545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80153494514430783671224363 120230241771646175506836545)
    ·
      refine ⟨90172681328734631630127409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120230241771646175506836545 90172681328734631630127409)
      ·
        refine ⟨67629510996550973722595557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90172681328734631630127409 67629510996550973722595557)
        ·
          refine ⟨12680533311853307572986667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67629510996550973722595557 12680533311853307572986667)
          ·
            refine ⟨19020799967779961359480001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12680533311853307572986667 19020799967779961359480001)
            ·
              refine ⟨14265599975834971019610001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19020799967779961359480001 14265599975834971019610001)
              ·
                refine ⟨10699199981876228264707501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14265599975834971019610001 10699199981876228264707501)
                ·
                  refine ⟨4012199993203585599265313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10699199981876228264707501 4012199993203585599265313)
                  ·
                    refine ⟨3009149994902689199448985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4012199993203585599265313 3009149994902689199448985)
                    ·
                      refine ⟨2256862496177016899586739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009149994902689199448985 2256862496177016899586739)
                      ·
                        rfl

theorem cell23_4395224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_4395224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395224 prefixEnd_4395224 := by exact prefixLift 4395224
  have htrace : WordTrace (prefixWord ++ tailWord_4395224) baseStart_4395224 baseEnd_4395224 := by
    simpa [prefixWord, tailWord_4395224, baseEnd_4395224] using wordTrace_append hprefix tailTrace_4395224
  have hstable : (prefixWord ++ tailWord_4395224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395224).length < 2 ^ (prefixWord ++ tailWord_4395224).sum := by decide
  have hdescent : baseEnd_4395224 < baseStart_4395224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395235 : List Nat := [1, 1, 1, 8, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4395235 : Nat := 118140960795 + 4395235 * 2 ^ 59
def prefixEnd_4395235 : Nat := 4983230072969 + 3 ^ 40 * 4395235 * 2
def baseEnd_4395235 : Nat := 2256868144464216356549189

theorem tailTrace_4395235 : CollatzResearch.WordTrace tailWord_4395235 prefixEnd_4395235 2256868144464216356549189 := by
  unfold tailWord_4395235
  simp only [CollatzResearch.WordTrace]
  refine ⟨160307390231821716221099159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106871593487881144147399439 160307390231821716221099159)
  ·
    refine ⟨240461085347732574331648739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160307390231821716221099159 240461085347732574331648739)
    ·
      refine ⟨360691628021598861497473109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240461085347732574331648739 360691628021598861497473109)
      ·
        refine ⟨4226855015878111658173513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 360691628021598861497473109 4226855015878111658173513)
        ·
          refine ⟨3170141261908583743630135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4226855015878111658173513 3170141261908583743630135)
          ·
            refine ⟨4755211892862875615445203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170141261908583743630135 4755211892862875615445203)
            ·
              refine ⟨7132817839294313423167805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755211892862875615445203 7132817839294313423167805)
              ·
                refine ⟨2674806689735367533687927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7132817839294313423167805 2674806689735367533687927)
                ·
                  refine ⟨4012210034603051300531891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674806689735367533687927 4012210034603051300531891)
                  ·
                    refine ⟨6018315051904576950797837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012210034603051300531891 6018315051904576950797837)
                    ·
                      refine ⟨2256868144464216356549189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018315051904576950797837 2256868144464216356549189)
                      ·
                        rfl

theorem cell23_4395235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4395235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395235 prefixEnd_4395235 := by exact prefixLift 4395235
  have htrace : WordTrace (prefixWord ++ tailWord_4395235) baseStart_4395235 baseEnd_4395235 := by
    simpa [prefixWord, tailWord_4395235, baseEnd_4395235] using wordTrace_append hprefix tailTrace_4395235
  have hstable : (prefixWord ++ tailWord_4395235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395235).length < 2 ^ (prefixWord ++ tailWord_4395235).sum := by decide
  have hdescent : baseEnd_4395235 < baseStart_4395235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395258 : List Nat := [3, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2]
def baseStart_4395258 : Nat := 118140960795 + 4395258 * 2 ^ 59
def prefixEnd_4395258 : Nat := 4983230072969 + 3 ^ 40 * 4395258 * 2
def baseEnd_4395258 : Nat := 2256879954519269766561583

theorem tailTrace_4395258 : CollatzResearch.WordTrace tailWord_4395258 prefixEnd_4395258 2256879954519269766561583 := by
  unfold tailWord_4395258
  simp only [CollatzResearch.WordTrace]
  refine ⟨40077057277684597787296607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106872152740492260766124285 40077057277684597787296607)
  ·
    refine ⟨60115585916526896680944911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40077057277684597787296607 60115585916526896680944911)
    ·
      refine ⟨90173378874790345021417367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60115585916526896680944911 90173378874790345021417367)
      ·
        refine ⟨135260068312185517532126051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90173378874790345021417367 135260068312185517532126051)
        ·
          refine ⟨202890102468278276298189077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135260068312185517532126051 202890102468278276298189077)
          ·
            refine ⟨9510473553200544201477613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 202890102468278276298189077 9510473553200544201477613)
            ·
              refine ⟨3566427582450204075554105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9510473553200544201477613 3566427582450204075554105)
              ·
                refine ⟨2674820686837653056665579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566427582450204075554105 2674820686837653056665579)
                ·
                  refine ⟨4012231030256479584998369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674820686837653056665579 4012231030256479584998369)
                  ·
                    refine ⟨3009173272692359688748777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4012231030256479584998369 3009173272692359688748777)
                    ·
                      refine ⟨2256879954519269766561583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009173272692359688748777 2256879954519269766561583)
                      ·
                        rfl

theorem cell23_4395258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_4395258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395258 prefixEnd_4395258 := by exact prefixLift 4395258
  have htrace : WordTrace (prefixWord ++ tailWord_4395258) baseStart_4395258 baseEnd_4395258 := by
    simpa [prefixWord, tailWord_4395258, baseEnd_4395258] using wordTrace_append hprefix tailTrace_4395258
  have hstable : (prefixWord ++ tailWord_4395258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395258).length < 2 ^ (prefixWord ++ tailWord_4395258).sum := by decide
  have hdescent : baseEnd_4395258 < baseStart_4395258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395267 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 3, 3, 2]
def baseStart_4395267 : Nat := 118140960795 + 4395267 * 2 ^ 59
def prefixEnd_4395267 : Nat := 4983230072969 + 3 ^ 40 * 4395267 * 2
def baseEnd_4395267 : Nat := 2256884575845160231349041

theorem tailTrace_4395267 : CollatzResearch.WordTrace tailWord_4395267 prefixEnd_4395267 2256884575845160231349041 := by
  unfold tailWord_4395267
  simp only [CollatzResearch.WordTrace]
  refine ⟨160308557367705785686264055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106872371578470523790842703 160308557367705785686264055)
  ·
    refine ⟨240462836051558678529396083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160308557367705785686264055 240462836051558678529396083)
    ·
      refine ⟨360694254077338017794094125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240462836051558678529396083 360694254077338017794094125)
      ·
        refine ⟨135260345279001756672785297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360694254077338017794094125 135260345279001756672785297)
        ·
          refine ⟨101445258959251317504588973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135260345279001756672785297 101445258959251317504588973)
          ·
            refine ⟨38041972109719244064220865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101445258959251317504588973 38041972109719244064220865)
            ·
              refine ⟨28531479082289433048165649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38041972109719244064220865 28531479082289433048165649)
              ·
                refine ⟨21398609311717074786124237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28531479082289433048165649 21398609311717074786124237)
                ·
                  refine ⟨8024478491893903044796589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21398609311717074786124237 8024478491893903044796589)
                  ·
                    refine ⟨3009179434460213641798721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8024478491893903044796589 3009179434460213641798721)
                    ·
                      refine ⟨2256884575845160231349041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009179434460213641798721 2256884575845160231349041)
                      ·
                        rfl

theorem cell23_4395267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_4395267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395267 prefixEnd_4395267 := by exact prefixLift 4395267
  have htrace : WordTrace (prefixWord ++ tailWord_4395267) baseStart_4395267 baseEnd_4395267 := by
    simpa [prefixWord, tailWord_4395267, baseEnd_4395267] using wordTrace_append hprefix tailTrace_4395267
  have hstable : (prefixWord ++ tailWord_4395267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395267).length < 2 ^ (prefixWord ++ tailWord_4395267).sum := by decide
  have hdescent : baseEnd_4395267 < baseStart_4395267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395268 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_4395268 : Nat := 118140960795 + 4395268 * 2 ^ 59
def prefixEnd_4395268 : Nat := 4983230072969 + 3 ^ 40 * 4395268 * 2
def baseEnd_4395268 : Nat := 752295029775271575812179

theorem tailTrace_4395268 : CollatzResearch.WordTrace tailWord_4395268 prefixEnd_4395268 752295029775271575812179 := by
  unfold tailWord_4395268
  simp only [CollatzResearch.WordTrace]
  refine ⟨80154296920351081428525229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106872395893801441904700305 80154296920351081428525229)
  ·
    refine ⟨30057861345131655535696961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80154296920351081428525229 30057861345131655535696961)
    ·
      refine ⟨22543396008848741651772721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30057861345131655535696961 22543396008848741651772721)
      ·
        refine ⟨16907547006636556238829541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22543396008848741651772721 16907547006636556238829541)
        ·
          refine ⟨3170165063744354294780539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16907547006636556238829541 3170165063744354294780539)
          ·
            refine ⟨4755247595616531442170809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170165063744354294780539 4755247595616531442170809)
            ·
              refine ⟨3566435696712398581628107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4755247595616531442170809 3566435696712398581628107)
              ·
                refine ⟨5349653545068597872442161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566435696712398581628107 5349653545068597872442161)
                ·
                  refine ⟨4012240158801448404331621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5349653545068597872442161 4012240158801448404331621)
                  ·
                    refine ⟨752295029775271575812179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012240158801448404331621 752295029775271575812179)
                    ·
                      rfl

theorem cell23_4395268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_4395268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395268 prefixEnd_4395268 := by exact prefixLift 4395268
  have htrace : WordTrace (prefixWord ++ tailWord_4395268) baseStart_4395268 baseEnd_4395268 := by
    simpa [prefixWord, tailWord_4395268, baseEnd_4395268] using wordTrace_append hprefix tailTrace_4395268
  have hstable : (prefixWord ++ tailWord_4395268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395268).length < 2 ^ (prefixWord ++ tailWord_4395268).sum := by decide
  have hdescent : baseEnd_4395268 < baseStart_4395268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395297 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_4395297 : Nat := 118140960795 + 4395297 * 2 ^ 59
def prefixEnd_4395297 : Nat := 4983230072969 + 3 ^ 40 * 4395297 * 2
def baseEnd_4395297 : Nat := 2256899980264795113973903

theorem tailTrace_4395297 : CollatzResearch.WordTrace tailWord_4395297 prefixEnd_4395297 2256899980264795113973903 := by
  unfold tailWord_4395297
  simp only [CollatzResearch.WordTrace]
  refine ⟨160309651557597100809856145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106873101038398067206570763 160309651557597100809856145)
  ·
    refine ⟨120232238668197825607392109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160309651557597100809856145 120232238668197825607392109)
    ·
      refine ⟨45087089500574184602772041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120232238668197825607392109 45087089500574184602772041)
      ·
        refine ⟨33815317125430638452079031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45087089500574184602772041 33815317125430638452079031)
        ·
          refine ⟨50722975688145957678118547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33815317125430638452079031 50722975688145957678118547)
          ·
            refine ⟨76084463532218936517177821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50722975688145957678118547 76084463532218936517177821)
            ·
              refine ⟨28531673824582101193941683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76084463532218936517177821 28531673824582101193941683)
              ·
                refine ⟨42797510736873151790912525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28531673824582101193941683 42797510736873151790912525)
                ·
                  refine ⟨16049066526327431921592197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42797510736873151790912525 16049066526327431921592197)
                  ·
                    refine ⟨3009199973686393485298537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16049066526327431921592197 3009199973686393485298537)
                    ·
                      refine ⟨2256899980264795113973903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009199973686393485298537 2256899980264795113973903)
                      ·
                        rfl

theorem cell23_4395297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_4395297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395297 prefixEnd_4395297 := by exact prefixLift 4395297
  have htrace : WordTrace (prefixWord ++ tailWord_4395297) baseStart_4395297 baseEnd_4395297 := by
    simpa [prefixWord, tailWord_4395297, baseEnd_4395297] using wordTrace_append hprefix tailTrace_4395297
  have hstable : (prefixWord ++ tailWord_4395297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395297).length < 2 ^ (prefixWord ++ tailWord_4395297).sum := by decide
  have hdescent : baseEnd_4395297 < baseStart_4395297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395309 : List Nat := [1, 5, 3, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_4395309 : Nat := 118140960795 + 4395309 * 2 ^ 59
def prefixEnd_4395309 : Nat := 4983230072969 + 3 ^ 40 * 4395309 * 2
def baseEnd_4395309 : Nat := 2256906142032649067023849

theorem tailTrace_4395309 : CollatzResearch.WordTrace tailWord_4395309 prefixEnd_4395309 2256906142032649067023849 := by
  unfold tailWord_4395309
  simp only [CollatzResearch.WordTrace]
  refine ⟨160310089233553626859292981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106873392822369084572861987 160310089233553626859292981)
  ·
    refine ⟨15029070865645652518058717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160310089233553626859292981 15029070865645652518058717)
    ·
      refine ⟨5635901574617119694272019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15029070865645652518058717 5635901574617119694272019)
      ·
        refine ⟨8453852361925679541408029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5635901574617119694272019 8453852361925679541408029)
        ·
          refine ⟨3170194635722129828028011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8453852361925679541408029 3170194635722129828028011)
          ·
            refine ⟨4755291953583194742042017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170194635722129828028011 4755291953583194742042017)
            ·
              refine ⟨3566468965187396056531513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4755291953583194742042017 3566468965187396056531513)
              ·
                refine ⟨2674851723890547042398635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566468965187396056531513 2674851723890547042398635)
                ·
                  refine ⟨4012277585835820563597953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674851723890547042398635 4012277585835820563597953)
                  ·
                    refine ⟨3009208189376865422698465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4012277585835820563597953 3009208189376865422698465)
                    ·
                      refine ⟨2256906142032649067023849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009208189376865422698465 2256906142032649067023849)
                      ·
                        rfl

theorem cell23_4395309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_4395309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395309 prefixEnd_4395309 := by exact prefixLift 4395309
  have htrace : WordTrace (prefixWord ++ tailWord_4395309) baseStart_4395309 baseEnd_4395309 := by
    simpa [prefixWord, tailWord_4395309, baseEnd_4395309] using wordTrace_append hprefix tailTrace_4395309
  have hstable : (prefixWord ++ tailWord_4395309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395309).length < 2 ^ (prefixWord ++ tailWord_4395309).sum := by decide
  have hdescent : baseEnd_4395309 < baseStart_4395309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395382 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4395382 : Nat := 118140960795 + 4395382 * 2 ^ 59
def prefixEnd_4395382 : Nat := 4983230072969 + 3 ^ 40 * 4395382 * 2
def baseEnd_4395382 : Nat := 2256943626120427281411013

theorem tailTrace_4395382 : CollatzResearch.WordTrace tailWord_4395382 prefixEnd_4395382 2256943626120427281411013 := by
  unfold tailWord_4395382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10019546985143072520418775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106875167841526106884466933 10019546985143072520418775)
  ·
    refine ⟨15029320477714608780628163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10019546985143072520418775 15029320477714608780628163)
    ·
      refine ⟨22543980716571913170942245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15029320477714608780628163 22543980716571913170942245)
      ·
        refine ⟨4226996384357233719551671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22543980716571913170942245 4226996384357233719551671)
        ·
          refine ⟨6340494576535850579327507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4226996384357233719551671 6340494576535850579327507)
          ·
            refine ⟨9510741864803775868991261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6340494576535850579327507 9510741864803775868991261)
            ·
              refine ⟨3566528199301415950871723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9510741864803775868991261 3566528199301415950871723)
              ·
                refine ⟨5349792298952123926307585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566528199301415950871723 5349792298952123926307585)
                ·
                  refine ⟨4012344224214092944730689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5349792298952123926307585 4012344224214092944730689)
                  ·
                    refine ⟨3009258168160569708548017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4012344224214092944730689 3009258168160569708548017)
                    ·
                      refine ⟨2256943626120427281411013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009258168160569708548017 2256943626120427281411013)
                      ·
                        rfl

theorem cell23_4395382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4395382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395382 prefixEnd_4395382 := by exact prefixLift 4395382
  have htrace : WordTrace (prefixWord ++ tailWord_4395382) baseStart_4395382 baseEnd_4395382 := by
    simpa [prefixWord, tailWord_4395382, baseEnd_4395382] using wordTrace_append hprefix tailTrace_4395382
  have hstable : (prefixWord ++ tailWord_4395382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395382).length < 2 ^ (prefixWord ++ tailWord_4395382).sum := by decide
  have hdescent : baseEnd_4395382 < baseStart_4395382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395424 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3]
def baseStart_4395424 : Nat := 118140960795 + 4395424 * 2 ^ 59
def prefixEnd_4395424 : Nat := 4983230072969 + 3 ^ 40 * 4395424 * 2
def baseEnd_4395424 : Nat := 2256965192307916117085819

theorem tailTrace_4395424 : CollatzResearch.WordTrace tailWord_4395424 prefixEnd_4395424 2256965192307916117085819 := by
  unfold tailWord_4395424
  simp only [CollatzResearch.WordTrace]
  refine ⟨80157141814068500749864663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106876189085424667666486217 80157141814068500749864663)
  ·
    refine ⟨120235712721102751124796995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80157141814068500749864663 120235712721102751124796995)
    ·
      refine ⟨180353569081654126687195493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120235712721102751124796995 180353569081654126687195493)
      ·
        refine ⟨33816294202810148753849155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180353569081654126687195493 33816294202810148753849155)
        ·
          refine ⟨50724441304215223130773733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33816294202810148753849155 50724441304215223130773733)
          ·
            refine ⟨9510832744540354337020075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50724441304215223130773733 9510832744540354337020075)
            ·
              refine ⟨14266249116810531505530113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9510832744540354337020075 14266249116810531505530113)
              ·
                refine ⟨10699686837607898629147585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14266249116810531505530113 10699686837607898629147585)
                ·
                  refine ⟨8024765128205923971860689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10699686837607898629147585 8024765128205923971860689)
                  ·
                    refine ⟨6018573846154442978895517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8024765128205923971860689 6018573846154442978895517)
                    ·
                      refine ⟨2256965192307916117085819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018573846154442978895517 2256965192307916117085819)
                      ·
                        rfl

theorem cell23_4395424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_4395424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395424 prefixEnd_4395424 := by exact prefixLift 4395424
  have htrace : WordTrace (prefixWord ++ tailWord_4395424) baseStart_4395424 baseEnd_4395424 := by
    simpa [prefixWord, tailWord_4395424, baseEnd_4395424] using wordTrace_append hprefix tailTrace_4395424
  have hstable : (prefixWord ++ tailWord_4395424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395424).length < 2 ^ (prefixWord ++ tailWord_4395424).sum := by decide
  have hdescent : baseEnd_4395424 < baseStart_4395424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395431 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 3, 4]
def baseStart_4395431 : Nat := 118140960795 + 4395431 * 2 ^ 59
def prefixEnd_4395431 : Nat := 4983230072969 + 3 ^ 40 * 4395431 * 2
def baseEnd_4395431 : Nat := 752322928890832529899429

theorem tailTrace_4395431 : CollatzResearch.WordTrace tailWord_4395431 prefixEnd_4395431 752322928890832529899429 := by
  unfold tailWord_4395431
  simp only [CollatzResearch.WordTrace]
  refine ⟨160314538939111641695234147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106876359292741094463489431 160314538939111641695234147)
  ·
    refine ⟨240471808408667462542851221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160314538939111641695234147 240471808408667462542851221)
    ·
      refine ⟨11272116019156287306696151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 240471808408667462542851221 11272116019156287306696151)
      ·
        refine ⟨16908174028734430960044227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272116019156287306696151 16908174028734430960044227)
        ·
          refine ⟨25362261043101646440066341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16908174028734430960044227 25362261043101646440066341)
          ·
            refine ⟨4755423945581558707512439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25362261043101646440066341 4755423945581558707512439)
            ·
              refine ⟨7133135918372338061268659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755423945581558707512439 7133135918372338061268659)
              ·
                refine ⟨10699703877558507091902989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7133135918372338061268659 10699703877558507091902989)
                ·
                  refine ⟨4012388954084440159463621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10699703877558507091902989 4012388954084440159463621)
                  ·
                    refine ⟨752322928890832529899429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012388954084440159463621 752322928890832529899429)
                    ·
                      rfl

theorem cell23_4395431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_4395431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395431 prefixEnd_4395431 := by exact prefixLift 4395431
  have htrace : WordTrace (prefixWord ++ tailWord_4395431) baseStart_4395431 baseEnd_4395431 := by
    simpa [prefixWord, tailWord_4395431, baseEnd_4395431] using wordTrace_append hprefix tailTrace_4395431
  have hstable : (prefixWord ++ tailWord_4395431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395431).length < 2 ^ (prefixWord ++ tailWord_4395431).sum := by decide
  have hdescent : baseEnd_4395431 < baseStart_4395431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395471 : List Nat := [1, 1, 2, 1, 1, 4, 1, 7, 1, 1, 3]
def baseStart_4395471 : Nat := 118140960795 + 4395471 * 2 ^ 59
def prefixEnd_4395471 : Nat := 4983230072969 + 3 ^ 40 * 4395471 * 2
def baseEnd_4395471 : Nat := 2256989325898677433198103

theorem tailTrace_4395471 : CollatzResearch.WordTrace tailWord_4395471 prefixEnd_4395471 2256989325898677433198103 := by
  unfold tailWord_4395471
  simp only [CollatzResearch.WordTrace]
  refine ⟨160315997858966728526690267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106877331905977819017793511 160315997858966728526690267)
  ·
    refine ⟨240473996788450092790035401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160315997858966728526690267 240473996788450092790035401)
    ·
      refine ⟨180355497591337569592526551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240473996788450092790035401 180355497591337569592526551)
      ·
        refine ⟨270533246387006354388789827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180355497591337569592526551 270533246387006354388789827)
        ·
          refine ⟨405799869580509531583184741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270533246387006354388789827 405799869580509531583184741)
          ·
            refine ⟨76087475546345537171847139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 405799869580509531583184741 76087475546345537171847139)
            ·
              refine ⟨114131213319518305757770709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76087475546345537171847139 114131213319518305757770709)
              ·
                refine ⟨2674950312176210291197751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114131213319518305757770709 2674950312176210291197751)
                ·
                  refine ⟨4012425468264315436796627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674950312176210291197751 4012425468264315436796627)
                  ·
                    refine ⟨6018638202396473155194941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012425468264315436796627 6018638202396473155194941)
                    ·
                      refine ⟨2256989325898677433198103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018638202396473155194941 2256989325898677433198103)
                      ·
                        rfl

theorem cell23_4395471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 1, 3].length) (baseStart_4395471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395471 prefixEnd_4395471 := by exact prefixLift 4395471
  have htrace : WordTrace (prefixWord ++ tailWord_4395471) baseStart_4395471 baseEnd_4395471 := by
    simpa [prefixWord, tailWord_4395471, baseEnd_4395471] using wordTrace_append hprefix tailTrace_4395471
  have hstable : (prefixWord ++ tailWord_4395471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395471).length < 2 ^ (prefixWord ++ tailWord_4395471).sum := by decide
  have hdescent : baseEnd_4395471 < baseStart_4395471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395504 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 2, 4]
def baseStart_4395504 : Nat := 118140960795 + 4395504 * 2 ^ 59
def prefixEnd_4395504 : Nat := 4983230072969 + 3 ^ 40 * 4395504 * 2
def baseEnd_4395504 : Nat := 752335423586758601361817

theorem tailTrace_4395504 : CollatzResearch.WordTrace tailWord_4395504 prefixEnd_4395504 752335423586758601361817 := by
  unfold tailWord_4395504
  simp only [CollatzResearch.WordTrace]
  refine ⟨80158600733923587581320783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106878134311898116775094377 80158600733923587581320783)
  ·
    refine ⟨120237901100885381371981175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80158600733923587581320783 120237901100885381371981175)
    ·
      refine ⟨180356851651328072057971763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120237901100885381371981175 180356851651328072057971763)
      ·
        refine ⟨270535277476992108086957645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180356851651328072057971763 270535277476992108086957645)
        ·
          refine ⟨101450729053872040532609117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270535277476992108086957645 101450729053872040532609117)
          ·
            refine ⟨38044023395202015199728419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101450729053872040532609117 38044023395202015199728419)
            ·
              refine ⟨57066035092803022799592629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38044023395202015199728419 57066035092803022799592629)
              ·
                refine ⟨5349940789950283387461809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57066035092803022799592629 5349940789950283387461809)
                ·
                  refine ⟨4012455592462712540596357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5349940789950283387461809 4012455592462712540596357)
                  ·
                    refine ⟨752335423586758601361817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012455592462712540596357 752335423586758601361817)
                    ·
                      rfl

theorem cell23_4395504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_4395504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395504 prefixEnd_4395504 := by exact prefixLift 4395504
  have htrace : WordTrace (prefixWord ++ tailWord_4395504) baseStart_4395504 baseEnd_4395504 := by
    simpa [prefixWord, tailWord_4395504, baseEnd_4395504] using wordTrace_append hprefix tailTrace_4395504
  have hstable : (prefixWord ++ tailWord_4395504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395504).length < 2 ^ (prefixWord ++ tailWord_4395504).sum := by decide
  have hdescent : baseEnd_4395504 < baseStart_4395504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395522 : List Nat := [3, 4, 1, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4395522 : Nat := 118140960795 + 4395522 * 2 ^ 59
def prefixEnd_4395522 : Nat := 4983230072969 + 3 ^ 40 * 4395522 * 2
def baseEnd_4395522 : Nat := 2257015513412056733660369

theorem tailTrace_4395522 : CollatzResearch.WordTrace tailWord_4395522 prefixEnd_4395522 2257015513412056733660369 := by
  unfold tailWord_4395522
  simp only [CollatzResearch.WordTrace]
  refine ⟨40079464495445491059199205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106878571987854642824531213 40079464495445491059199205)
  ·
    refine ⟨7514899592896029573599851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40079464495445491059199205 7514899592896029573599851)
    ·
      refine ⟨11272349389344044360399777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7514899592896029573599851 11272349389344044360399777)
      ·
        refine ⟨8454262042008033270299833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11272349389344044360399777 8454262042008033270299833)
        ·
          refine ⟨6340696531506024952724875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8454262042008033270299833 6340696531506024952724875)
          ·
            refine ⟨9511044797259037429087313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6340696531506024952724875 9511044797259037429087313)
            ·
              refine ⟨7133283597944278071815485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9511044797259037429087313 7133283597944278071815485)
              ·
                refine ⟨2674981349229104276930807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7133283597944278071815485 2674981349229104276930807)
                ·
                  refine ⟨4012472023843656415396211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674981349229104276930807 4012472023843656415396211)
                  ·
                    refine ⟨6018708035765484623094317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012472023843656415396211 6018708035765484623094317)
                    ·
                      refine ⟨2257015513412056733660369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018708035765484623094317 2257015513412056733660369)
                      ·
                        rfl

theorem cell23_4395522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4395522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395522 prefixEnd_4395522 := by exact prefixLift 4395522
  have htrace : WordTrace (prefixWord ++ tailWord_4395522) baseStart_4395522 baseEnd_4395522 := by
    simpa [prefixWord, tailWord_4395522, baseEnd_4395522] using wordTrace_append hprefix tailTrace_4395522
  have hstable : (prefixWord ++ tailWord_4395522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395522).length < 2 ^ (prefixWord ++ tailWord_4395522).sum := by decide
  have hdescent : baseEnd_4395522 < baseStart_4395522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395531 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 3]
def baseStart_4395531 : Nat := 118140960795 + 4395531 * 2 ^ 59
def prefixEnd_4395531 : Nat := 4983230072969 + 3 ^ 40 * 4395531 * 2
def baseEnd_4395531 : Nat := 2257020134737947198447827

theorem tailTrace_4395531 : CollatzResearch.WordTrace tailWord_4395531 prefixEnd_4395531 2257020134737947198447827 := by
  unfold tailWord_4395531
  simp only [CollatzResearch.WordTrace]
  refine ⟨160318186238749358773874447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106878790825832905849249631 160318186238749358773874447)
  ·
    refine ⟨240477279358124038160811671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160318186238749358773874447 240477279358124038160811671)
    ·
      refine ⟨360715919037186057241217507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240477279358124038160811671 360715919037186057241217507)
      ·
        refine ⟨541073878555779085861826261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360715919037186057241217507 541073878555779085861826261)
        ·
          refine ⟨12681419028651072324886553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 541073878555779085861826261 12681419028651072324886553)
          ·
            refine ⟨9511064271488304243664915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12681419028651072324886553 9511064271488304243664915)
            ·
              refine ⟨14266596407232456365497373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9511064271488304243664915 14266596407232456365497373)
              ·
                refine ⟨5349973652712171137061515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14266596407232456365497373 5349973652712171137061515)
                ·
                  refine ⟨8024960479068256705592273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5349973652712171137061515 8024960479068256705592273)
                  ·
                    refine ⟨6018720359301192529194205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8024960479068256705592273 6018720359301192529194205)
                    ·
                      refine ⟨2257020134737947198447827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018720359301192529194205 2257020134737947198447827)
                      ·
                        rfl

theorem cell23_4395531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 3].length) (baseStart_4395531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395531 prefixEnd_4395531 := by exact prefixLift 4395531
  have htrace : WordTrace (prefixWord ++ tailWord_4395531) baseStart_4395531 baseEnd_4395531 := by
    simpa [prefixWord, tailWord_4395531, baseEnd_4395531] using wordTrace_append hprefix tailTrace_4395531
  have hstable : (prefixWord ++ tailWord_4395531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395531).length < 2 ^ (prefixWord ++ tailWord_4395531).sum := by decide
  have hdescent : baseEnd_4395531 < baseStart_4395531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395612 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_4395612 : Nat := 118140960795 + 4395612 * 2 ^ 59
def prefixEnd_4395612 : Nat := 4983230072969 + 3 ^ 40 * 4395612 * 2
def baseEnd_4395612 : Nat := 2257061726670961381534955

theorem tailTrace_4395612 : CollatzResearch.WordTrace tailWord_4395612 prefixEnd_4395612 2257061726670961381534955 := by
  unfold tailWord_4395612
  simp only [CollatzResearch.WordTrace]
  refine ⟨80160570275727954803786545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106880760367637273071715393 80160570275727954803786545)
  ·
    refine ⟨60120427706795966102839909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80160570275727954803786545 60120427706795966102839909)
    ·
      refine ⟨11272580195024243644282483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60120427706795966102839909 11272580195024243644282483)
      ·
        refine ⟨16908870292536365466423725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272580195024243644282483 16908870292536365466423725)
        ·
          refine ⟨6340826359701137049908897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16908870292536365466423725 6340826359701137049908897)
          ·
            refine ⟨4755619769775852787431673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6340826359701137049908897 4755619769775852787431673)
            ·
              refine ⟨3566714827331889590573755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4755619769775852787431673 3566714827331889590573755)
              ·
                refine ⟨5350072240997834385860633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566714827331889590573755 5350072240997834385860633)
                ·
                  refine ⟨4012554180748375789395475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5350072240997834385860633 4012554180748375789395475)
                  ·
                    refine ⟨6018831271122563684093213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012554180748375789395475 6018831271122563684093213)
                    ·
                      refine ⟨2257061726670961381534955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018831271122563684093213 2257061726670961381534955)
                      ·
                        rfl

theorem cell23_4395612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_4395612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395612 prefixEnd_4395612 := by exact prefixLift 4395612
  have htrace : WordTrace (prefixWord ++ tailWord_4395612) baseStart_4395612 baseEnd_4395612 := by
    simpa [prefixWord, tailWord_4395612, baseEnd_4395612] using wordTrace_append hprefix tailTrace_4395612
  have hstable : (prefixWord ++ tailWord_4395612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395612).length < 2 ^ (prefixWord ++ tailWord_4395612).sum := by decide
  have hdescent : baseEnd_4395612 < baseStart_4395612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395658 : List Nat := [3, 1, 2, 3, 3, 1, 1, 4, 5]
def baseStart_4395658 : Nat := 118140960795 + 4395658 * 2 ^ 59
def prefixEnd_4395658 : Nat := 4983230072969 + 3 ^ 40 * 4395658 * 2
def baseEnd_4395658 : Nat := 250787260753452022395527

theorem tailTrace_4395658 : CollatzResearch.WordTrace tailWord_4395658 prefixEnd_4395658 250787260753452022395527 := by
  unfold tailWord_4395658
  simp only [CollatzResearch.WordTrace]
  refine ⟨40080704577322314865936907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106881878872859506309165085 40080704577322314865936907)
  ·
    refine ⟨60121056865983472298905361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40080704577322314865936907 60121056865983472298905361)
    ·
      refine ⟨45090792649487604224179021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60121056865983472298905361 45090792649487604224179021)
      ·
        refine ⟨16909047243557851584067133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45090792649487604224179021 16909047243557851584067133)
        ·
          refine ⟨6340892716334194344025175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16909047243557851584067133 6340892716334194344025175)
          ·
            refine ⟨9511339074501291516037763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6340892716334194344025175 9511339074501291516037763)
            ·
              refine ⟨14267008611751937274056645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9511339074501291516037763 14267008611751937274056645)
              ·
                refine ⟨2675064114703488238885621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14267008611751937274056645 2675064114703488238885621)
                ·
                  refine ⟨250787260753452022395527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2675064114703488238885621 250787260753452022395527)
                  ·
                    rfl

theorem cell23_4395658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_4395658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395658 prefixEnd_4395658 := by exact prefixLift 4395658
  have htrace : WordTrace (prefixWord ++ tailWord_4395658) baseStart_4395658 baseEnd_4395658 := by
    simpa [prefixWord, tailWord_4395658, baseEnd_4395658] using wordTrace_append hprefix tailTrace_4395658
  have hstable : (prefixWord ++ tailWord_4395658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395658).length < 2 ^ (prefixWord ++ tailWord_4395658).sum := by decide
  have hdescent : baseEnd_4395658 < baseStart_4395658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395668 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4395668 : Nat := 118140960795 + 4395668 * 2 ^ 59
def prefixEnd_4395668 : Nat := 4983230072969 + 3 ^ 40 * 4395668 * 2
def baseEnd_4395668 : Nat := 2257090481587613162434697

theorem tailTrace_4395668 : CollatzResearch.WordTrace tailWord_4395668 prefixEnd_4395668 2257090481587613162434697 := by
  unfold tailWord_4395668
  simp only [CollatzResearch.WordTrace]
  refine ⟨80161591519626515585805829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106882122026168687447741105 80161591519626515585805829)
  ·
    refine ⟨15030298409929971672338593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80161591519626515585805829 15030298409929971672338593)
    ·
      refine ⟨11272723807447478754253945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15030298409929971672338593 11272723807447478754253945)
      ·
        refine ⟨8454542855585609065690459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11272723807447478754253945 8454542855585609065690459)
        ·
          refine ⟨12681814283378413598535689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8454542855585609065690459 12681814283378413598535689)
          ·
            refine ⟨9511360712533810198901767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12681814283378413598535689 9511360712533810198901767)
            ·
              refine ⟨14267041068800715298352651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9511360712533810198901767 14267041068800715298352651)
              ·
                refine ⟨21400561603201072947528977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14267041068800715298352651 21400561603201072947528977)
                ·
                  refine ⟨16050421202400804710646733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21400561603201072947528977 16050421202400804710646733)
                  ·
                    refine ⟨6018907950900301766492525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16050421202400804710646733 6018907950900301766492525)
                    ·
                      refine ⟨2257090481587613162434697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6018907950900301766492525 2257090481587613162434697)
                      ·
                        rfl

theorem cell23_4395668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4395668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395668 prefixEnd_4395668 := by exact prefixLift 4395668
  have htrace : WordTrace (prefixWord ++ tailWord_4395668) baseStart_4395668 baseEnd_4395668 := by
    simpa [prefixWord, tailWord_4395668, baseEnd_4395668] using wordTrace_append hprefix tailTrace_4395668
  have hstable : (prefixWord ++ tailWord_4395668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395668).length < 2 ^ (prefixWord ++ tailWord_4395668).sum := by decide
  have hdescent : baseEnd_4395668 < baseStart_4395668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395678 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_4395678 : Nat := 118140960795 + 4395678 * 2 ^ 59
def prefixEnd_4395678 : Nat := 4983230072969 + 3 ^ 40 * 4395678 * 2
def baseEnd_4395678 : Nat := 2257095616394158123309651

theorem tailTrace_4395678 : CollatzResearch.WordTrace tailWord_4395678 prefixEnd_4395678 2257095616394158123309651 := by
  unfold tailWord_4395678
  simp only [CollatzResearch.WordTrace]
  refine ⟨20040443471152100359934461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106882365179477868586317125 20040443471152100359934461)
  ·
    refine ⟨7515166301682037634975423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20040443471152100359934461 7515166301682037634975423)
    ·
      refine ⟨11272749452523056452463135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7515166301682037634975423 11272749452523056452463135)
      ·
        refine ⟨16909124178784584678694703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272749452523056452463135 16909124178784584678694703)
        ·
          refine ⟨25363686268176877018042055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16909124178784584678694703 25363686268176877018042055)
          ·
            refine ⟨38045529402265315527063083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25363686268176877018042055 38045529402265315527063083)
            ·
              refine ⟨57068294103397973290594625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38045529402265315527063083 57068294103397973290594625)
              ·
                refine ⟨42801220577548479967945969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57068294103397973290594625 42801220577548479967945969)
                ·
                  refine ⟨32100915433161359975959477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42801220577548479967945969 32100915433161359975959477)
                  ·
                    refine ⟨3009460821858877497746201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32100915433161359975959477 3009460821858877497746201)
                    ·
                      refine ⟨2257095616394158123309651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009460821858877497746201 2257095616394158123309651)
                      ·
                        rfl

theorem cell23_4395678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_4395678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395678 prefixEnd_4395678 := by exact prefixLift 4395678
  have htrace : WordTrace (prefixWord ++ tailWord_4395678) baseStart_4395678 baseEnd_4395678 := by
    simpa [prefixWord, tailWord_4395678, baseEnd_4395678] using wordTrace_append hprefix tailTrace_4395678
  have hstable : (prefixWord ++ tailWord_4395678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395678).length < 2 ^ (prefixWord ++ tailWord_4395678).sum := by decide
  have hdescent : baseEnd_4395678 < baseStart_4395678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395752 : List Nat := [2, 1, 4, 1, 4, 2, 1, 3, 1, 4]
def baseStart_4395752 : Nat := 118140960795 + 4395752 * 2 ^ 59
def prefixEnd_4395752 : Nat := 4983230072969 + 3 ^ 40 * 4395752 * 2
def baseEnd_4395752 : Nat := 752377871320863611261437

theorem tailTrace_4395752 : CollatzResearch.WordTrace tailWord_4395752 prefixEnd_4395752 752377871320863611261437 := by
  unfold tailWord_4395752
  simp only [CollatzResearch.WordTrace]
  refine ⟨80163123385474356758834755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106884164513965809011779673 80163123385474356758834755)
  ·
    refine ⟨120244685078211535138252133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80163123385474356758834755 120244685078211535138252133)
    ·
      refine ⟨22545878452164662838422275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120244685078211535138252133 22545878452164662838422275)
      ·
        refine ⟨33818817678246994257633413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22545878452164662838422275 33818817678246994257633413)
        ·
          refine ⟨6341028314671311423306265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33818817678246994257633413 6341028314671311423306265)
          ·
            refine ⟨4755771236003483567479699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6341028314671311423306265 4755771236003483567479699)
            ·
              refine ⟨7133656854005225351219549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755771236003483567479699 7133656854005225351219549)
              ·
                refine ⟨2675121320251959506707331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7133656854005225351219549 2675121320251959506707331)
                ·
                  refine ⟨4012681980377939260060997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675121320251959506707331 4012681980377939260060997)
                  ·
                    refine ⟨752377871320863611261437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012681980377939260060997 752377871320863611261437)
                    ·
                      rfl

theorem cell23_4395752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_4395752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395752 prefixEnd_4395752 := by exact prefixLift 4395752
  have htrace : WordTrace (prefixWord ++ tailWord_4395752) baseStart_4395752 baseEnd_4395752 := by
    simpa [prefixWord, tailWord_4395752, baseEnd_4395752] using wordTrace_append hprefix tailTrace_4395752
  have hstable : (prefixWord ++ tailWord_4395752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395752).length < 2 ^ (prefixWord ++ tailWord_4395752).sum := by decide
  have hdescent : baseEnd_4395752 < baseStart_4395752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395761 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 1, 5]
def baseStart_4395761 : Nat := 118140960795 + 4395761 * 2 ^ 59
def prefixEnd_4395761 : Nat := 4983230072969 + 3 ^ 40 * 4395761 * 2
def baseEnd_4395761 : Nat := 752379411762827099523923

theorem tailTrace_4395761 : CollatzResearch.WordTrace tailWord_4395761 prefixEnd_4395761 752379411762827099523923 := by
  unfold tailWord_4395761
  simp only [CollatzResearch.WordTrace]
  refine ⟨160326575027916108054747137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106884383351944072036498091 160326575027916108054747137)
  ·
    refine ⟨120244931270937081041060353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160326575027916108054747137 120244931270937081041060353)
    ·
      refine ⟨90183698453202810780795265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120244931270937081041060353 90183698453202810780795265)
      ·
        refine ⟨67637773839902108085596449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90183698453202810780795265 67637773839902108085596449)
        ·
          refine ⟨50728330379926581064197337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67637773839902108085596449 50728330379926581064197337)
          ·
            refine ⟨38046247784944935798148003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50728330379926581064197337 38046247784944935798148003)
            ·
              refine ⟨57069371677417403697222005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38046247784944935798148003 57069371677417403697222005)
              ·
                refine ⟨5350253594757881596614563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57069371677417403697222005 5350253594757881596614563)
                ·
                  refine ⟨8025380392136822394921845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5350253594757881596614563 8025380392136822394921845)
                  ·
                    refine ⟨752379411762827099523923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8025380392136822394921845 752379411762827099523923)
                    ·
                      rfl

theorem cell23_4395761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_4395761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395761 prefixEnd_4395761 := by exact prefixLift 4395761
  have htrace : WordTrace (prefixWord ++ tailWord_4395761) baseStart_4395761 baseEnd_4395761 := by
    simpa [prefixWord, tailWord_4395761, baseEnd_4395761] using wordTrace_append hprefix tailTrace_4395761
  have hstable : (prefixWord ++ tailWord_4395761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395761).length < 2 ^ (prefixWord ++ tailWord_4395761).sum := by decide
  have hdescent : baseEnd_4395761 < baseStart_4395761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395768 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 2, 3, 2]
def baseStart_4395768 : Nat := 118140960795 + 4395768 * 2 ^ 59
def prefixEnd_4395768 : Nat := 4983230072969 + 3 ^ 40 * 4395768 * 2
def baseEnd_4395768 : Nat := 2257141829653062771184237

theorem tailTrace_4395768 : CollatzResearch.WordTrace tailWord_4395768 prefixEnd_4395768 2257141829653062771184237 := by
  unfold tailWord_4395768
  simp only [CollatzResearch.WordTrace]
  refine ⟨80163415169445374125125979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106884553559260498833501305 80163415169445374125125979)
  ·
    refine ⟨120245122754168061187688969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80163415169445374125125979 120245122754168061187688969)
    ·
      refine ⟨90183842065626045890766727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120245122754168061187688969 90183842065626045890766727)
      ·
        refine ⟨135275763098439068836150091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90183842065626045890766727 135275763098439068836150091)
        ·
          refine ⟨202913644647658603254225137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135275763098439068836150091 202913644647658603254225137)
          ·
            refine ⟨152185233485743952440668853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202913644647658603254225137 152185233485743952440668853)
            ·
              refine ⟨14267365639288495541312705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152185233485743952440668853 14267365639288495541312705)
              ·
                refine ⟨10700524229466371655984529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14267365639288495541312705 10700524229466371655984529)
                ·
                  refine ⟨8025393172099778741988397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10700524229466371655984529 8025393172099778741988397)
                  ·
                    refine ⟨3009522439537417028245649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8025393172099778741988397 3009522439537417028245649)
                    ·
                      refine ⟨2257141829653062771184237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009522439537417028245649 2257141829653062771184237)
                      ·
                        rfl

theorem cell23_4395768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_4395768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395768 prefixEnd_4395768 := by exact prefixLift 4395768
  have htrace : WordTrace (prefixWord ++ tailWord_4395768) baseStart_4395768 baseEnd_4395768 := by
    simpa [prefixWord, tailWord_4395768, baseEnd_4395768] using wordTrace_append hprefix tailTrace_4395768
  have hstable : (prefixWord ++ tailWord_4395768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395768).length < 2 ^ (prefixWord ++ tailWord_4395768).sum := by decide
  have hdescent : baseEnd_4395768 < baseStart_4395768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395831 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_4395831 : Nat := 118140960795 + 4395831 * 2 ^ 59
def prefixEnd_4395831 : Nat := 4983230072969 + 3 ^ 40 * 4395831 * 2
def baseEnd_4395831 : Nat := 2257174178934296024696447

theorem tailTrace_4395831 : CollatzResearch.WordTrace tailWord_4395831 prefixEnd_4395831 2257174178934296024696447 := by
  unfold tailWord_4395831
  simp only [CollatzResearch.WordTrace]
  refine ⟨160329128137662510009795347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106886085425108340006530231 160329128137662510009795347)
  ·
    refine ⟨240493692206493765014693021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160329128137662510009795347 240493692206493765014693021)
    ·
      refine ⟨90185134577435161880509883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240493692206493765014693021 90185134577435161880509883)
      ·
        refine ⟨135277701866152742820764825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90185134577435161880509883 135277701866152742820764825)
        ·
          refine ⟨101458276399614557115573619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135277701866152742820764825 101458276399614557115573619)
          ·
            refine ⟨152187414599421835673360429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101458276399614557115573619 152187414599421835673360429)
            ·
              refine ⟨57070280474783188377510161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152187414599421835673360429 57070280474783188377510161)
              ·
                refine ⟨42802710356087391283132621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57070280474783188377510161 42802710356087391283132621)
                ·
                  refine ⟨16051016383532771731174733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42802710356087391283132621 16051016383532771731174733)
                  ·
                    refine ⟨6019131143824789399190525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16051016383532771731174733 6019131143824789399190525)
                    ·
                      refine ⟨2257174178934296024696447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6019131143824789399190525 2257174178934296024696447)
                      ·
                        rfl

theorem cell23_4395831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_4395831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395831 prefixEnd_4395831 := by exact prefixLift 4395831
  have htrace : WordTrace (prefixWord ++ tailWord_4395831) baseStart_4395831 baseEnd_4395831 := by
    simpa [prefixWord, tailWord_4395831, baseEnd_4395831] using wordTrace_append hprefix tailTrace_4395831
  have hstable : (prefixWord ++ tailWord_4395831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395831).length < 2 ^ (prefixWord ++ tailWord_4395831).sum := by decide
  have hdescent : baseEnd_4395831 < baseStart_4395831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395832 : List Nat := [2, 1, 2, 1, 3, 2, 3, 4, 1, 2, 2]
def baseStart_4395832 : Nat := 118140960795 + 4395832 * 2 ^ 59
def prefixEnd_4395832 : Nat := 4983230072969 + 3 ^ 40 * 4395832 * 2
def baseEnd_4395832 : Nat := 2257174692414950520783943

theorem tailTrace_4395832 : CollatzResearch.WordTrace tailWord_4395832 prefixEnd_4395832 2257174692414950520783943 := by
  unfold tailWord_4395832
  simp only [CollatzResearch.WordTrace]
  refine ⟨80164582305329443590290875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106886109740439258120387833 80164582305329443590290875)
  ·
    refine ⟨120246873457994165385436313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80164582305329443590290875 120246873457994165385436313)
    ·
      refine ⟨90185155093495624039077235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120246873457994165385436313 90185155093495624039077235)
      ·
        refine ⟨135277732640243436058615853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90185155093495624039077235 135277732640243436058615853)
        ·
          refine ⟨50729149740091288521980945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135277732640243436058615853 50729149740091288521980945)
          ·
            refine ⟨38046862305068466391485709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50729149740091288521980945 38046862305068466391485709)
            ·
              refine ⟨14267573364400674896807141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38046862305068466391485709 14267573364400674896807141)
              ·
                refine ⟨2675170005825126543151339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14267573364400674896807141 2675170005825126543151339)
                ·
                  refine ⟨4012755008737689814727009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675170005825126543151339 4012755008737689814727009)
                  ·
                    refine ⟨3009566256553267361045257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4012755008737689814727009 3009566256553267361045257)
                    ·
                      refine ⟨2257174692414950520783943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009566256553267361045257 2257174692414950520783943)
                      ·
                        rfl

theorem cell23_4395832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_4395832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395832 prefixEnd_4395832 := by exact prefixLift 4395832
  have htrace : WordTrace (prefixWord ++ tailWord_4395832) baseStart_4395832 baseEnd_4395832 := by
    simpa [prefixWord, tailWord_4395832, baseEnd_4395832] using wordTrace_append hprefix tailTrace_4395832
  have hstable : (prefixWord ++ tailWord_4395832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395832).length < 2 ^ (prefixWord ++ tailWord_4395832).sum := by decide
  have hdescent : baseEnd_4395832 < baseStart_4395832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395848 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_4395848 : Nat := 118140960795 + 4395848 * 2 ^ 59
def prefixEnd_4395848 : Nat := 4983230072969 + 3 ^ 40 * 4395848 * 2
def baseEnd_4395848 : Nat := 2257182908105422458183869

theorem tailTrace_4395848 : CollatzResearch.WordTrace tailWord_4395848 prefixEnd_4395848 2257182908105422458183869 := by
  unfold tailWord_4395848
  simp only [CollatzResearch.WordTrace]
  refine ⟨80164874089300460956582099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106886498785733947942109465 80164874089300460956582099)
  ·
    refine ⟨120247311133950691434873149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80164874089300460956582099 120247311133950691434873149)
    ·
      refine ⟨45092741675231509288077431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120247311133950691434873149 45092741675231509288077431)
      ·
        refine ⟨67639112512847263932116147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45092741675231509288077431 67639112512847263932116147)
        ·
          refine ⟨101458668769270895898174221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67639112512847263932116147 101458668769270895898174221)
          ·
            refine ⟨38047000788476585961815333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101458668769270895898174221 38047000788476585961815333)
            ·
              refine ⟨7133812647839359867840375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38047000788476585961815333 7133812647839359867840375)
              ·
                refine ⟨10700718971759039801760563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7133812647839359867840375 10700718971759039801760563)
                ·
                  refine ⟨16051078457638559702640845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10700718971759039801760563 16051078457638559702640845)
                  ·
                    refine ⟨6019154421614459888490317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16051078457638559702640845 6019154421614459888490317)
                    ·
                      refine ⟨2257182908105422458183869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6019154421614459888490317 2257182908105422458183869)
                      ·
                        rfl

theorem cell23_4395848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_4395848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395848 prefixEnd_4395848 := by exact prefixLift 4395848
  have htrace : WordTrace (prefixWord ++ tailWord_4395848) baseStart_4395848 baseEnd_4395848 := by
    simpa [prefixWord, tailWord_4395848, baseEnd_4395848] using wordTrace_append hprefix tailTrace_4395848
  have hstable : (prefixWord ++ tailWord_4395848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395848).length < 2 ^ (prefixWord ++ tailWord_4395848).sum := by decide
  have hdescent : baseEnd_4395848 < baseStart_4395848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395861 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4395861 : Nat := 118140960795 + 4395861 * 2 ^ 59
def prefixEnd_4395861 : Nat := 4983230072969 + 3 ^ 40 * 4395861 * 2
def baseEnd_4395861 : Nat := 2257189583353930907321309

theorem tailTrace_4395861 : CollatzResearch.WordTrace tailWord_4395861 prefixEnd_4395861 2257189583353930907321309 := by
  unfold tailWord_4395861
  simp only [CollatzResearch.WordTrace]
  refine ⟨160330222327553825133387437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106886814885035883422258291 160330222327553825133387437)
  ·
    refine ⟨60123833372832684425020289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160330222327553825133387437 60123833372832684425020289)
    ·
      refine ⟨45092875029624513318765217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60123833372832684425020289 45092875029624513318765217)
      ·
        refine ⟨33819656272218384989073913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45092875029624513318765217 33819656272218384989073913)
        ·
          refine ⟨25364742204163788741805435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33819656272218384989073913 25364742204163788741805435)
          ·
            refine ⟨38047113306245683112708153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25364742204163788741805435 38047113306245683112708153)
            ·
              refine ⟨28535334979684262334531115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38047113306245683112708153 28535334979684262334531115)
              ·
                refine ⟨42803002469526393501796673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28535334979684262334531115 42803002469526393501796673)
                ·
                  refine ⟨32102251852144795126347505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42803002469526393501796673 32102251852144795126347505)
                  ·
                    refine ⟨24076688889108596344760629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32102251852144795126347505 24076688889108596344760629)
                    ·
                      refine ⟨2257189583353930907321309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24076688889108596344760629 2257189583353930907321309)
                      ·
                        rfl

theorem cell23_4395861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4395861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395861 prefixEnd_4395861 := by exact prefixLift 4395861
  have htrace : WordTrace (prefixWord ++ tailWord_4395861) baseStart_4395861 baseEnd_4395861 := by
    simpa [prefixWord, tailWord_4395861, baseEnd_4395861] using wordTrace_append hprefix tailTrace_4395861
  have hstable : (prefixWord ++ tailWord_4395861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395861).length < 2 ^ (prefixWord ++ tailWord_4395861).sum := by decide
  have hdescent : baseEnd_4395861 < baseStart_4395861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395888 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 3, 4, 2]
def baseStart_4395888 : Nat := 118140960795 + 4395888 * 2 ^ 59
def prefixEnd_4395888 : Nat := 4983230072969 + 3 ^ 40 * 4395888 * 2
def baseEnd_4395888 : Nat := 2257203447331602301683685

theorem tailTrace_4395888 : CollatzResearch.WordTrace tailWord_4395888 prefixEnd_4395888 2257203447331602301683685 := by
  unfold tailWord_4395888
  simp only [CollatzResearch.WordTrace]
  refine ⟨80165603549228004372310159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106887471398970672496413545 80165603549228004372310159)
  ·
    refine ⟨120248405323842006558465239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80165603549228004372310159 120248405323842006558465239)
    ·
      refine ⟨180372607985763009837697859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120248405323842006558465239 180372607985763009837697859)
      ·
        refine ⟨270558911978644514756546789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180372607985763009837697859 270558911978644514756546789)
        ·
          refine ⟨50729795995995846516852523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270558911978644514756546789 50729795995995846516852523)
          ·
            refine ⟨76094693993993769775278785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50729795995995846516852523 76094693993993769775278785)
            ·
              refine ⟨57071020495495327331459089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76094693993993769775278785 57071020495495327331459089)
              ·
                refine ⟨42803265371621495498594317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57071020495495327331459089 42803265371621495498594317)
                ·
                  refine ⟨16051224514358060811972869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42803265371621495498594317 16051224514358060811972869)
                  ·
                    refine ⟨3009604596442136402244913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16051224514358060811972869 3009604596442136402244913)
                    ·
                      refine ⟨2257203447331602301683685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009604596442136402244913 2257203447331602301683685)
                      ·
                        rfl

theorem cell23_4395888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 4, 2].length) (baseStart_4395888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395888 prefixEnd_4395888 := by exact prefixLift 4395888
  have htrace : WordTrace (prefixWord ++ tailWord_4395888) baseStart_4395888 baseEnd_4395888 := by
    simpa [prefixWord, tailWord_4395888, baseEnd_4395888] using wordTrace_append hprefix tailTrace_4395888
  have hstable : (prefixWord ++ tailWord_4395888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395888).length < 2 ^ (prefixWord ++ tailWord_4395888).sum := by decide
  have hdescent : baseEnd_4395888 < baseStart_4395888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395891 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 3]
def baseStart_4395891 : Nat := 118140960795 + 4395891 * 2 ^ 59
def prefixEnd_4395891 : Nat := 4983230072969 + 3 ^ 40 * 4395891 * 2
def baseEnd_4395891 : Nat := 2257204987773565789946171

theorem tailTrace_4395891 : CollatzResearch.WordTrace tailWord_4395891 prefixEnd_4395891 2257204987773565789946171 := by
  unfold tailWord_4395891
  simp only [CollatzResearch.WordTrace]
  refine ⟨160331316517445140256979527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106887544344963426837986351 160331316517445140256979527)
  ·
    refine ⟨240496974776167710385469291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160331316517445140256979527 240496974776167710385469291)
    ·
      refine ⟨360745462164251565578203937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240496974776167710385469291 360745462164251565578203937)
      ·
        refine ⟨270559096623188674183652953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360745462164251565578203937 270559096623188674183652953)
        ·
          refine ⟨202919322467391505637739715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270559096623188674183652953 202919322467391505637739715)
          ·
            refine ⟨304378983701087258456609573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202919322467391505637739715 304378983701087258456609573)
            ·
              refine ⟨57071059443953860960614295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304378983701087258456609573 57071059443953860960614295)
              ·
                refine ⟨85606589165930791440921443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57071059443953860960614295 85606589165930791440921443)
                ·
                  refine ⟨128409883748896187161382165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85606589165930791440921443 128409883748896187161382165)
                  ·
                    refine ⟨6019213300729508773189789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 128409883748896187161382165 6019213300729508773189789)
                    ·
                      refine ⟨2257204987773565789946171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6019213300729508773189789 2257204987773565789946171)
                      ·
                        rfl

theorem cell23_4395891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_4395891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395891 prefixEnd_4395891 := by exact prefixLift 4395891
  have htrace : WordTrace (prefixWord ++ tailWord_4395891) baseStart_4395891 baseEnd_4395891 := by
    simpa [prefixWord, tailWord_4395891, baseEnd_4395891] using wordTrace_append hprefix tailTrace_4395891
  have hstable : (prefixWord ++ tailWord_4395891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395891).length < 2 ^ (prefixWord ++ tailWord_4395891).sum := by decide
  have hdescent : baseEnd_4395891 < baseStart_4395891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395926 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4395926 : Nat := 118140960795 + 4395926 * 2 ^ 59
def prefixEnd_4395926 : Nat := 4983230072969 + 3 ^ 40 * 4395926 * 2
def baseEnd_4395926 : Nat := 2257222959596473153008511

theorem tailTrace_4395926 : CollatzResearch.WordTrace tailWord_4395926 prefixEnd_4395926 2257222959596473153008511 := by
  unfold tailWord_4395926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10020787067019896327156477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106888395381545560823002421 10020787067019896327156477)
  ·
    refine ⟨3757795150132461122683679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10020787067019896327156477 3757795150132461122683679)
    ·
      refine ⟨5636692725198691684025519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757795150132461122683679 5636692725198691684025519)
      ·
        refine ⟨8455039087798037526038279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5636692725198691684025519 8455039087798037526038279)
        ·
          refine ⟨12682558631697056289057419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8455039087798037526038279 12682558631697056289057419)
          ·
            refine ⟨19023837947545584433586129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12682558631697056289057419 19023837947545584433586129)
            ·
              refine ⟨14267878460659188325189597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19023837947545584433586129 14267878460659188325189597)
              ·
                refine ⟨5350454422747195621946099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14267878460659188325189597 5350454422747195621946099)
                ·
                  refine ⟨8025681634120793432919149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5350454422747195621946099 8025681634120793432919149)
                  ·
                    refine ⟨3009630612795297537344681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8025681634120793432919149 3009630612795297537344681)
                    ·
                      refine ⟨2257222959596473153008511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009630612795297537344681 2257222959596473153008511)
                      ·
                        rfl

theorem cell23_4395926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4395926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395926 prefixEnd_4395926 := by exact prefixLift 4395926
  have htrace : WordTrace (prefixWord ++ tailWord_4395926) baseStart_4395926 baseEnd_4395926 := by
    simpa [prefixWord, tailWord_4395926, baseEnd_4395926] using wordTrace_append hprefix tailTrace_4395926
  have hstable : (prefixWord ++ tailWord_4395926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395926).length < 2 ^ (prefixWord ++ tailWord_4395926).sum := by decide
  have hdescent : baseEnd_4395926 < baseStart_4395926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395945 : List Nat := [1, 2, 1, 1, 1, 1, 9, 2, 5]
def baseStart_4395945 : Nat := 118140960795 + 4395945 * 2 ^ 59
def prefixEnd_4395945 : Nat := 4983230072969 + 3 ^ 40 * 4395945 * 2
def baseEnd_4395945 : Nat := 250803635080989842074547

theorem tailTrace_4395945 : CollatzResearch.WordTrace tailWord_4395945 prefixEnd_4395945 250803635080989842074547 := by
  unfold tailWord_4395945
  simp only [CollatzResearch.WordTrace]
  refine ⟨160333286059249507479445289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106888857372833004986296859 160333286059249507479445289)
  ·
    refine ⟨120249964544437130609583967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160333286059249507479445289 120249964544437130609583967)
    ·
      refine ⟨180374946816655695914375951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120249964544437130609583967 180374946816655695914375951)
      ·
        refine ⟨270562420224983543871563927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180374946816655695914375951 270562420224983543871563927)
        ·
          refine ⟨405843630337475315807345891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270562420224983543871563927 405843630337475315807345891)
          ·
            refine ⟨608765445506212973711018837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405843630337475315807345891 608765445506212973711018837)
            ·
              refine ⟨3566985032262966642838001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 608765445506212973711018837 3566985032262966642838001)
              ·
                refine ⟨2675238774197224982128501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566985032262966642838001 2675238774197224982128501)
                ·
                  refine ⟨250803635080989842074547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2675238774197224982128501 250803635080989842074547)
                  ·
                    rfl

theorem cell23_4395945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 5].length) (baseStart_4395945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395945 prefixEnd_4395945 := by exact prefixLift 4395945
  have htrace : WordTrace (prefixWord ++ tailWord_4395945) baseStart_4395945 baseEnd_4395945 := by
    simpa [prefixWord, tailWord_4395945, baseEnd_4395945] using wordTrace_append hprefix tailTrace_4395945
  have hstable : (prefixWord ++ tailWord_4395945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395945).length < 2 ^ (prefixWord ++ tailWord_4395945).sum := by decide
  have hdescent : baseEnd_4395945 < baseStart_4395945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395948 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 7, 2]
def baseStart_4395948 : Nat := 118140960795 + 4395948 * 2 ^ 59
def prefixEnd_4395948 : Nat := 4983230072969 + 3 ^ 40 * 4395948 * 2
def baseEnd_4395948 : Nat := 2257234256170872066933409

theorem tailTrace_4395948 : CollatzResearch.WordTrace tailWord_4395948 prefixEnd_4395948 2257234256170872066933409 := by
  unfold tailWord_4395948
  simp only [CollatzResearch.WordTrace]
  refine ⟨80166697739119319495902249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106888930318825759327869665 80166697739119319495902249)
  ·
    refine ⟨60125023304339489621926687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80166697739119319495902249 60125023304339489621926687)
    ·
      refine ⟨90187534956509234432890031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60125023304339489621926687 90187534956509234432890031)
      ·
        refine ⟨135281302434763851649335047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90187534956509234432890031 135281302434763851649335047)
        ·
          refine ⟨202921953652145777474002571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135281302434763851649335047 202921953652145777474002571)
          ·
            refine ⟨304382930478218666211003857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202921953652145777474002571 304382930478218666211003857)
            ·
              refine ⟨228287197858663999658252893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304382930478218666211003857 228287197858663999658252893)
              ·
                refine ⟨85607699196998999871844835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228287197858663999658252893 85607699196998999871844835)
                ·
                  refine ⟨128411548795498499807767253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85607699196998999871844835 128411548795498499807767253)
                  ·
                    refine ⟨3009645674894496089244545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 128411548795498499807767253 3009645674894496089244545)
                    ·
                      refine ⟨2257234256170872066933409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009645674894496089244545 2257234256170872066933409)
                      ·
                        rfl

theorem cell23_4395948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_4395948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395948 prefixEnd_4395948 := by exact prefixLift 4395948
  have htrace : WordTrace (prefixWord ++ tailWord_4395948) baseStart_4395948 baseEnd_4395948 := by
    simpa [prefixWord, tailWord_4395948, baseEnd_4395948] using wordTrace_append hprefix tailTrace_4395948
  have hstable : (prefixWord ++ tailWord_4395948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395948).length < 2 ^ (prefixWord ++ tailWord_4395948).sum := by decide
  have hdescent : baseEnd_4395948 < baseStart_4395948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4395956 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4395956 : Nat := 118140960795 + 4395956 * 2 ^ 59
def prefixEnd_4395956 : Nat := 4983230072969 + 3 ^ 40 * 4395956 * 2
def baseEnd_4395956 : Nat := 2257238364016108035633373

theorem tailTrace_4395956 : CollatzResearch.WordTrace tailWord_4395956 prefixEnd_4395956 2257238364016108035633373 := by
  unfold tailWord_4395956
  simp only [CollatzResearch.WordTrace]
  refine ⟨80166843631104828179047861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106889124841473104238730481 80166843631104828179047861)
  ·
    refine ⟨7515641590416077641785737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80166843631104828179047861 7515641590416077641785737)
    ·
      refine ⟨5636731192812058231339303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7515641590416077641785737 5636731192812058231339303)
      ·
        refine ⟨8455096789218087347008955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5636731192812058231339303 8455096789218087347008955)
        ·
          refine ⟨12682645183827131020513433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8455096789218087347008955 12682645183827131020513433)
          ·
            refine ⟨9511983887870348265385075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12682645183827131020513433 9511983887870348265385075)
            ·
              refine ⟨14267975831805522398077613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9511983887870348265385075 14267975831805522398077613)
              ·
                refine ⟨5350490936927070899279105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14267975831805522398077613 5350490936927070899279105)
                ·
                  refine ⟨4012868202695303174459329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5350490936927070899279105 4012868202695303174459329)
                  ·
                    refine ⟨3009651152021477380844497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4012868202695303174459329 3009651152021477380844497)
                    ·
                      refine ⟨2257238364016108035633373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009651152021477380844497 2257238364016108035633373)
                      ·
                        rfl

theorem cell23_4395956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4395956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4395956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4395956 prefixEnd_4395956 := by exact prefixLift 4395956
  have htrace : WordTrace (prefixWord ++ tailWord_4395956) baseStart_4395956 baseEnd_4395956 := by
    simpa [prefixWord, tailWord_4395956, baseEnd_4395956] using wordTrace_append hprefix tailTrace_4395956
  have hstable : (prefixWord ++ tailWord_4395956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4395956).length < 2 ^ (prefixWord ++ tailWord_4395956).sum := by decide
  have hdescent : baseEnd_4395956 < baseStart_4395956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4395956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396022 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_4396022 : Nat := 118140960795 + 4396022 * 2 ^ 59
def prefixEnd_4396022 : Nat := 4983230072969 + 3 ^ 40 * 4396022 * 2
def baseEnd_4396022 : Nat := 752424084579768259136023

theorem tailTrace_4396022 : CollatzResearch.WordTrace tailWord_4396022 prefixEnd_4396022 752424084579768259136023 := by
  unfold tailWord_4396022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10021005904998159351874895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106890729653313699753332213 10021005904998159351874895)
  ·
    refine ⟨15031508857497239027812343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10021005904998159351874895 15031508857497239027812343)
    ·
      refine ⟨22547263286245858541718515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15031508857497239027812343 22547263286245858541718515)
      ·
        refine ⟨33820894929368787812577773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22547263286245858541718515 33820894929368787812577773)
        ·
          refine ⟨12682835598513295429716665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33820894929368787812577773 12682835598513295429716665)
          ·
            refine ⟨9512126698884971572287499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12682835598513295429716665 9512126698884971572287499)
            ·
              refine ⟨14268190048327457358431249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9512126698884971572287499 14268190048327457358431249)
              ·
                refine ⟨10701142536245593018823437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14268190048327457358431249 10701142536245593018823437)
                ·
                  refine ⟨4012928451092097382058789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10701142536245593018823437 4012928451092097382058789)
                  ·
                    refine ⟨752424084579768259136023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012928451092097382058789 752424084579768259136023)
                    ·
                      rfl

theorem cell23_4396022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_4396022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396022 prefixEnd_4396022 := by exact prefixLift 4396022
  have htrace : WordTrace (prefixWord ++ tailWord_4396022) baseStart_4396022 baseEnd_4396022 := by
    simpa [prefixWord, tailWord_4396022, baseEnd_4396022] using wordTrace_append hprefix tailTrace_4396022
  have hstable : (prefixWord ++ tailWord_4396022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396022).length < 2 ^ (prefixWord ++ tailWord_4396022).sum := by decide
  have hdescent : baseEnd_4396022 < baseStart_4396022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396085 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_4396085 : Nat := 118140960795 + 4396085 * 2 ^ 59
def prefixEnd_4396085 : Nat := 4983230072969 + 3 ^ 40 * 4396085 * 2
def baseEnd_4396085 : Nat := 2257304603020538030920279

theorem tailTrace_4396085 : CollatzResearch.WordTrace tailWord_4396085 prefixEnd_4396085 2257304603020538030920279 := by
  unfold tailWord_4396085
  simp only [CollatzResearch.WordTrace]
  refine ⟨160338392278742311389541709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106892261519161540926361139 160338392278742311389541709)
  ·
    refine ⟨60126897104528366771078141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160338392278742311389541709 60126897104528366771078141)
    ·
      refine ⟨22547586414198137539154303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60126897104528366771078141 22547586414198137539154303)
      ·
        refine ⟨33821379621297206308731455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22547586414198137539154303 33821379621297206308731455)
        ·
          refine ⟨50732069431945809463097183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33821379621297206308731455 50732069431945809463097183)
          ·
            refine ⟨76098104147918714194645775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50732069431945809463097183 76098104147918714194645775)
            ·
              refine ⟨114147156221878071291968663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76098104147918714194645775 114147156221878071291968663)
              ·
                refine ⟨171220734332817106937952995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114147156221878071291968663 171220734332817106937952995)
                ·
                  refine ⟨256831101499225660406929493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171220734332817106937952995 256831101499225660406929493)
                  ·
                    refine ⟨3009739470694050707893705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 256831101499225660406929493 3009739470694050707893705)
                    ·
                      refine ⟨2257304603020538030920279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009739470694050707893705 2257304603020538030920279)
                      ·
                        rfl

theorem cell23_4396085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_4396085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396085 prefixEnd_4396085 := by exact prefixLift 4396085
  have htrace : WordTrace (prefixWord ++ tailWord_4396085) baseStart_4396085 baseEnd_4396085 := by
    simpa [prefixWord, tailWord_4396085, baseEnd_4396085] using wordTrace_append hprefix tailTrace_4396085
  have hstable : (prefixWord ++ tailWord_4396085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396085).length < 2 ^ (prefixWord ++ tailWord_4396085).sum := by decide
  have hdescent : baseEnd_4396085 < baseStart_4396085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396128 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_4396128 : Nat := 118140960795 + 4396128 * 2 ^ 59
def prefixEnd_4396128 : Nat := 4983230072969 + 3 ^ 40 * 4396128 * 2
def baseEnd_4396128 : Nat := 2257326682688681362682581

theorem tailTrace_4396128 : CollatzResearch.WordTrace tailWord_4396128 prefixEnd_4396128 2257326682688681362682581 := by
  unfold tailWord_4396128
  simp only [CollatzResearch.WordTrace]
  refine ⟨80169980308793264866678519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106893307078391019822238025 80169980308793264866678519)
  ·
    refine ⟨120254970463189897300017779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80169980308793264866678519 120254970463189897300017779)
    ·
      refine ⟨180382455694784845950026669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120254970463189897300017779 180382455694784845950026669)
      ·
        refine ⟨67643420885544317231260001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180382455694784845950026669 67643420885544317231260001)
        ·
          refine ⟨50732565664158237923445001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67643420885544317231260001 50732565664158237923445001)
          ·
            refine ⟨38049424248118678442583751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50732565664158237923445001 38049424248118678442583751)
            ·
              refine ⟨57074136372178017663875627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38049424248118678442583751 57074136372178017663875627)
              ·
                refine ⟨85611204558267026495813441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57074136372178017663875627 85611204558267026495813441)
                ·
                  refine ⟨64208403418700269871860081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85611204558267026495813441 64208403418700269871860081)
                  ·
                    refine ⟨48156302564025202403895061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64208403418700269871860081 48156302564025202403895061)
                    ·
                      refine ⟨2257326682688681362682581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48156302564025202403895061 2257326682688681362682581)
                      ·
                        rfl

theorem cell23_4396128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_4396128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396128 prefixEnd_4396128 := by exact prefixLift 4396128
  have htrace : WordTrace (prefixWord ++ tailWord_4396128) baseStart_4396128 baseEnd_4396128 := by
    simpa [prefixWord, tailWord_4396128, baseEnd_4396128] using wordTrace_append hprefix tailTrace_4396128
  have hstable : (prefixWord ++ tailWord_4396128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396128).length < 2 ^ (prefixWord ++ tailWord_4396128).sum := by decide
  have hdescent : baseEnd_4396128 < baseStart_4396128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396136 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4396136 : Nat := 118140960795 + 4396136 * 2 ^ 59
def prefixEnd_4396136 : Nat := 4983230072969 + 3 ^ 40 * 4396136 * 2
def baseEnd_4396136 : Nat := 2257330790533917331382545

theorem tailTrace_4396136 : CollatzResearch.WordTrace tailWord_4396136 prefixEnd_4396136 2257330790533917331382545 := by
  unfold tailWord_4396136
  simp only [CollatzResearch.WordTrace]
  refine ⟨80170126200778773549824131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106893501601038364733098841 80170126200778773549824131)
  ·
    refine ⟨120255189301168160324736197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80170126200778773549824131 120255189301168160324736197)
    ·
      refine ⟨22547847993969030060888037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120255189301168160324736197 22547847993969030060888037)
      ·
        refine ⟨4227721498869193136416507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22547847993969030060888037 4227721498869193136416507)
        ·
          refine ⟨6341582248303789704624761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4227721498869193136416507 6341582248303789704624761)
          ·
            refine ⟨4756186686227842278468571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6341582248303789704624761 4756186686227842278468571)
            ·
              refine ⟨7134280029341763417702857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756186686227842278468571 7134280029341763417702857)
              ·
                refine ⟨5350710022006322563277143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7134280029341763417702857 5350710022006322563277143)
                ·
                  refine ⟨8026065033009483844915715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5350710022006322563277143 8026065033009483844915715)
                  ·
                    refine ⟨12039097549514225767373573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8026065033009483844915715 12039097549514225767373573)
                    ·
                      refine ⟨2257330790533917331382545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12039097549514225767373573 2257330790533917331382545)
                      ·
                        rfl

theorem cell23_4396136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4396136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396136 prefixEnd_4396136 := by exact prefixLift 4396136
  have htrace : WordTrace (prefixWord ++ tailWord_4396136) baseStart_4396136 baseEnd_4396136 := by
    simpa [prefixWord, tailWord_4396136, baseEnd_4396136] using wordTrace_append hprefix tailTrace_4396136
  have hstable : (prefixWord ++ tailWord_4396136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396136).length < 2 ^ (prefixWord ++ tailWord_4396136).sum := by decide
  have hdescent : baseEnd_4396136 < baseStart_4396136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396149 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4396149 : Nat := 118140960795 + 4396149 * 2 ^ 59
def prefixEnd_4396149 : Nat := 4983230072969 + 3 ^ 40 * 4396149 * 2
def baseEnd_4396149 : Nat := 2257337465782425780519985

theorem tailTrace_4396149 : CollatzResearch.WordTrace tailWord_4396149 prefixEnd_4396149 2257337465782425780519985 := by
  unfold tailWord_4396149
  simp only [CollatzResearch.WordTrace]
  refine ⟨160340726550510450319871501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106893817700340300213247667 160340726550510450319871501)
  ·
    refine ⟨60127772456441418869951813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160340726550510450319871501 60127772456441418869951813)
    ·
      refine ⟨11273957335582766038115965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60127772456441418869951813 11273957335582766038115965)
      ·
        refine ⟨4227734000843537264293487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11273957335582766038115965 4227734000843537264293487)
        ·
          refine ⟨6341601001265305896440231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4227734000843537264293487 6341601001265305896440231)
          ·
            refine ⟨9512401501897958844660347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6341601001265305896440231 9512401501897958844660347)
            ·
              refine ⟨14268602252846938266990521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9512401501897958844660347 14268602252846938266990521)
              ·
                refine ⟨10701451689635203700242891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14268602252846938266990521 10701451689635203700242891)
                ·
                  refine ⟨16052177534452805550364337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10701451689635203700242891 16052177534452805550364337)
                  ·
                    refine ⟨12039133150839604162773253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16052177534452805550364337 12039133150839604162773253)
                    ·
                      refine ⟨2257337465782425780519985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12039133150839604162773253 2257337465782425780519985)
                      ·
                        rfl

theorem cell23_4396149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4396149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396149 prefixEnd_4396149 := by exact prefixLift 4396149
  have htrace : WordTrace (prefixWord ++ tailWord_4396149) baseStart_4396149 baseEnd_4396149 := by
    simpa [prefixWord, tailWord_4396149, baseEnd_4396149] using wordTrace_append hprefix tailTrace_4396149
  have hstable : (prefixWord ++ tailWord_4396149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396149).length < 2 ^ (prefixWord ++ tailWord_4396149).sum := by decide
  have hdescent : baseEnd_4396149 < baseStart_4396149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396169 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 3]
def baseStart_4396169 : Nat := 118140960795 + 4396169 * 2 ^ 59
def prefixEnd_4396169 : Nat := 4983230072969 + 3 ^ 40 * 4396169 * 2
def baseEnd_4396169 : Nat := 2257347735395515702269893

theorem tailTrace_4396169 : CollatzResearch.WordTrace tailWord_4396169 prefixEnd_4396169 2257347735395515702269893 := by
  unfold tailWord_4396169
  simp only [CollatzResearch.WordTrace]
  refine ⟨160341456010437993735599561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106894304006958662490399707 160341456010437993735599561)
  ·
    refine ⟨120256092007828495301699671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160341456010437993735599561 120256092007828495301699671)
    ·
      refine ⟨180384138011742742952549507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120256092007828495301699671 180384138011742742952549507)
      ·
        refine ⟨270576207017614114428824261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180384138011742742952549507 270576207017614114428824261)
        ·
          refine ⟨50733038815802646455404549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270576207017614114428824261 50733038815802646455404549)
          ·
            refine ⟨9512444777962996210388353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50733038815802646455404549 9512444777962996210388353)
            ·
              refine ⟨7134333583472247157791265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9512444777962996210388353 7134333583472247157791265)
              ·
                refine ⟨5350750187604185368343449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7134333583472247157791265 5350750187604185368343449)
                ·
                  refine ⟨4013062640703139026257587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5350750187604185368343449 4013062640703139026257587)
                  ·
                    refine ⟨6019593961054708539386381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4013062640703139026257587 6019593961054708539386381)
                    ·
                      refine ⟨2257347735395515702269893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6019593961054708539386381 2257347735395515702269893)
                      ·
                        rfl

theorem cell23_4396169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 3].length) (baseStart_4396169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396169 prefixEnd_4396169 := by exact prefixLift 4396169
  have htrace : WordTrace (prefixWord ++ tailWord_4396169) baseStart_4396169 baseEnd_4396169 := by
    simpa [prefixWord, tailWord_4396169, baseEnd_4396169] using wordTrace_append hprefix tailTrace_4396169
  have hstable : (prefixWord ++ tailWord_4396169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396169).length < 2 ^ (prefixWord ++ tailWord_4396169).sum := by decide
  have hdescent : baseEnd_4396169 < baseStart_4396169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396209 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4396209 : Nat := 118140960795 + 4396209 * 2 ^ 59
def prefixEnd_4396209 : Nat := 4983230072969 + 3 ^ 40 * 4396209 * 2
def baseEnd_4396209 : Nat := 2257368274621695545769709

theorem tailTrace_4396209 : CollatzResearch.WordTrace tailWord_4396209 prefixEnd_4396209 2257368274621695545769709 := by
  unfold tailWord_4396209
  simp only [CollatzResearch.WordTrace]
  refine ⟨160342914930293080567055681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106895276620195387044703787 160342914930293080567055681)
  ·
    refine ⟨120257186197719810425291761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160342914930293080567055681 120257186197719810425291761)
    ·
      refine ⟨90192889648289857818968821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120257186197719810425291761 90192889648289857818968821)
      ·
        refine ⟨8455583404527174170528327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90192889648289857818968821 8455583404527174170528327)
        ·
          refine ⟨12683375106790761255792491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8455583404527174170528327 12683375106790761255792491)
          ·
            refine ⟨19025062660186141883688737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12683375106790761255792491 19025062660186141883688737)
            ·
              refine ⟨14268796995139606412766553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19025062660186141883688737 14268796995139606412766553)
              ·
                refine ⟨10701597746354704809574915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14268796995139606412766553 10701597746354704809574915)
                ·
                  refine ⟨16052396619532057214362373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10701597746354704809574915 16052396619532057214362373)
                  ·
                    refine ⟨3009824366162260727692945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16052396619532057214362373 3009824366162260727692945)
                    ·
                      refine ⟨2257368274621695545769709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3009824366162260727692945 2257368274621695545769709)
                      ·
                        rfl

theorem cell23_4396209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4396209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396209 prefixEnd_4396209 := by exact prefixLift 4396209
  have htrace : WordTrace (prefixWord ++ tailWord_4396209) baseStart_4396209 baseEnd_4396209 := by
    simpa [prefixWord, tailWord_4396209, baseEnd_4396209] using wordTrace_append hprefix tailTrace_4396209
  have hstable : (prefixWord ++ tailWord_4396209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396209).length < 2 ^ (prefixWord ++ tailWord_4396209).sum := by decide
  have hdescent : baseEnd_4396209 < baseStart_4396209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396222 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4396222 : Nat := 118140960795 + 4396222 * 2 ^ 59
def prefixEnd_4396222 : Nat := 4983230072969 + 3 ^ 40 * 4396222 * 2
def baseEnd_4396222 : Nat := 2257374949870203994907149

theorem tailTrace_4396222 : CollatzResearch.WordTrace tailWord_4396222 prefixEnd_4396222 2257374949870203994907149 := by
  unfold tailWord_4396222
  simp only [CollatzResearch.WordTrace]
  refine ⟨20042923634905747973409865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106895592719497322524852613 20042923634905747973409865)
  ·
    refine ⟨15032192726179310980057399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20042923634905747973409865 15032192726179310980057399)
    ·
      refine ⟨22548289089268966470086099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15032192726179310980057399 22548289089268966470086099)
      ·
        refine ⟨33822433633903449705129149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22548289089268966470086099 33822433633903449705129149)
        ·
          refine ⟨12683412612713793639423431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33822433633903449705129149 12683412612713793639423431)
          ·
            refine ⟨19025118919070690459135147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12683412612713793639423431 19025118919070690459135147)
            ·
              refine ⟨28537678378606035688702721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19025118919070690459135147 28537678378606035688702721)
              ·
                refine ⟨21403258783954526766527041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28537678378606035688702721 21403258783954526766527041)
                ·
                  refine ⟨16052444087965895074895281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21403258783954526766527041 16052444087965895074895281)
                  ·
                    refine ⟨12039333065974421306171461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16052444087965895074895281 12039333065974421306171461)
                    ·
                      refine ⟨2257374949870203994907149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12039333065974421306171461 2257374949870203994907149)
                      ·
                        rfl

theorem cell23_4396222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4396222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396222 prefixEnd_4396222 := by exact prefixLift 4396222
  have htrace : WordTrace (prefixWord ++ tailWord_4396222) baseStart_4396222 baseEnd_4396222 := by
    simpa [prefixWord, tailWord_4396222, baseEnd_4396222] using wordTrace_append hprefix tailTrace_4396222
  have hstable : (prefixWord ++ tailWord_4396222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396222).length < 2 ^ (prefixWord ++ tailWord_4396222).sum := by decide
  have hdescent : baseEnd_4396222 < baseStart_4396222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396232 : List Nat := [2, 1, 3, 1, 2, 1, 4, 4, 5]
def baseStart_4396232 : Nat := 118140960795 + 4396232 * 2 ^ 59
def prefixEnd_4396232 : Nat := 4983230072969 + 3 ^ 40 * 4396232 * 2
def baseEnd_4396232 : Nat := 250820009408527661753567

theorem tailTrace_4396232 : CollatzResearch.WordTrace tailWord_4396232 prefixEnd_4396232 250820009408527661753567 := by
  unfold tailWord_4396232
  simp only [CollatzResearch.WordTrace]
  refine ⟨80171876904604877747571475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106895835872806503663428633 80171876904604877747571475)
  ·
    refine ⟨120257815356907316621357213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80171876904604877747571475 120257815356907316621357213)
    ·
      refine ⟨45096680758840243733008955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120257815356907316621357213 45096680758840243733008955)
      ·
        refine ⟨67645021138260365599513433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45096680758840243733008955 67645021138260365599513433)
        ·
          refine ⟨50733765853695274199635075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67645021138260365599513433 50733765853695274199635075)
          ·
            refine ⟨76100648780542911299452613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50733765853695274199635075 76100648780542911299452613)
            ·
              refine ⟨14268871646351795868647365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76100648780542911299452613 14268871646351795868647365)
              ·
                refine ⟨2675413433690961725371381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14268871646351795868647365 2675413433690961725371381)
                ·
                  refine ⟨250820009408527661753567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2675413433690961725371381 250820009408527661753567)
                  ·
                    rfl

theorem cell23_4396232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 5].length) (baseStart_4396232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396232 prefixEnd_4396232 := by exact prefixLift 4396232
  have htrace : WordTrace (prefixWord ++ tailWord_4396232) baseStart_4396232 baseEnd_4396232 := by
    simpa [prefixWord, tailWord_4396232, baseEnd_4396232] using wordTrace_append hprefix tailTrace_4396232
  have hstable : (prefixWord ++ tailWord_4396232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396232).length < 2 ^ (prefixWord ++ tailWord_4396232).sum := by decide
  have hdescent : baseEnd_4396232 < baseStart_4396232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396242 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_4396242 : Nat := 118140960795 + 4396242 * 2 ^ 59
def prefixEnd_4396242 : Nat := 4983230072969 + 3 ^ 40 * 4396242 * 2
def baseEnd_4396242 : Nat := 2257385219483293916657057

theorem tailTrace_4396242 : CollatzResearch.WordTrace tailWord_4396242 prefixEnd_4396242 2257385219483293916657057 := by
  unfold tailWord_4396242
  simp only [CollatzResearch.WordTrace]
  refine ⟨40086029634793381800751745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106896079026115684802004653 40086029634793381800751745)
  ·
    refine ⟨30064522226095036350563809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40086029634793381800751745 30064522226095036350563809)
    ·
      refine ⟨22548391669571277262922857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30064522226095036350563809 22548391669571277262922857)
      ·
        refine ⟨16911293752178457947192143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22548391669571277262922857 16911293752178457947192143)
        ·
          refine ⟨25366940628267686920788215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16911293752178457947192143 25366940628267686920788215)
          ·
            refine ⟨38050410942401530381182323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25366940628267686920788215 38050410942401530381182323)
            ·
              refine ⟨57075616413602295571773485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38050410942401530381182323 57075616413602295571773485)
              ·
                refine ⟨21403356155100860839415057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57075616413602295571773485 21403356155100860839415057)
                ·
                  refine ⟨16052517116325645629561293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21403356155100860839415057 16052517116325645629561293)
                  ·
                    refine ⟨6019693918622117111085485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16052517116325645629561293 6019693918622117111085485)
                    ·
                      refine ⟨2257385219483293916657057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6019693918622117111085485 2257385219483293916657057)
                      ·
                        rfl

theorem cell23_4396242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_4396242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396242 prefixEnd_4396242 := by exact prefixLift 4396242
  have htrace : WordTrace (prefixWord ++ tailWord_4396242) baseStart_4396242 baseEnd_4396242 := by
    simpa [prefixWord, tailWord_4396242, baseEnd_4396242] using wordTrace_append hprefix tailTrace_4396242
  have hstable : (prefixWord ++ tailWord_4396242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396242).length < 2 ^ (prefixWord ++ tailWord_4396242).sum := by decide
  have hdescent : baseEnd_4396242 < baseStart_4396242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396282 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_4396282 : Nat := 118140960795 + 4396282 * 2 ^ 59
def prefixEnd_4396282 : Nat := 4983230072969 + 3 ^ 40 * 4396282 * 2
def baseEnd_4396282 : Nat := 2257405758709473760156873

theorem tailTrace_4396282 : CollatzResearch.WordTrace tailWord_4396282 prefixEnd_4396282 2257405758709473760156873 := by
  unfold tailWord_4396282
  simp only [CollatzResearch.WordTrace]
  refine ⟨40086394364757153508615775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106897051639352409356308733 40086394364757153508615775)
  ·
    refine ⟨60129591547135730262923663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40086394364757153508615775 60129591547135730262923663)
    ·
      refine ⟨90194387320703595394385495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60129591547135730262923663 90194387320703595394385495)
      ·
        refine ⟨135291580981055393091578243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90194387320703595394385495 135291580981055393091578243)
        ·
          refine ⟨202937371471583089637367365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135291580981055393091578243 202937371471583089637367365)
          ·
            refine ⟨38050757150921829307006381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202937371471583089637367365 38050757150921829307006381)
            ·
              refine ⟨14269033931595685990127393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38050757150921829307006381 14269033931595685990127393)
              ·
                refine ⟨10701775448696764492595545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14269033931595685990127393 10701775448696764492595545)
                ·
                  refine ⟨8026331586522573369446659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10701775448696764492595545 8026331586522573369446659)
                  ·
                    refine ⟨12039497379783860054169989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8026331586522573369446659 12039497379783860054169989)
                    ·
                      refine ⟨2257405758709473760156873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12039497379783860054169989 2257405758709473760156873)
                      ·
                        rfl

theorem cell23_4396282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_4396282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396282 prefixEnd_4396282 := by exact prefixLift 4396282
  have htrace : WordTrace (prefixWord ++ tailWord_4396282) baseStart_4396282 baseEnd_4396282 := by
    simpa [prefixWord, tailWord_4396282, baseEnd_4396282] using wordTrace_append hprefix tailTrace_4396282
  have hstable : (prefixWord ++ tailWord_4396282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396282).length < 2 ^ (prefixWord ++ tailWord_4396282).sum := by decide
  have hdescent : baseEnd_4396282 < baseStart_4396282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396389 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_4396389 : Nat := 118140960795 + 4396389 * 2 ^ 59
def prefixEnd_4396389 : Nat := 4983230072969 + 3 ^ 40 * 4396389 * 2
def baseEnd_4396389 : Nat := 2257460701139504841518881

theorem tailTrace_4396389 : CollatzResearch.WordTrace tailWord_4396389 prefixEnd_4396389 2257460701139504841518881 := by
  unfold tailWord_4396389
  simp only [CollatzResearch.WordTrace]
  refine ⟨160349480069640971308608221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106899653379760647539072147 160349480069640971308608221)
  ·
    refine ⟨60131055026115364240728083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160349480069640971308608221 60131055026115364240728083)
    ·
      refine ⟨90196582539173046361092125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60131055026115364240728083 90196582539173046361092125)
      ·
        refine ⟨33823718452189892385409547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90196582539173046361092125 33823718452189892385409547)
        ·
          refine ⟨50735577678284838578114321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33823718452189892385409547 50735577678284838578114321)
          ·
            refine ⟨38051683258713628933585741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50735577678284838578114321 38051683258713628933585741)
            ·
              refine ⟨14269381222017610850094653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38051683258713628933585741 14269381222017610850094653)
              ·
                refine ⟨5351017958256604068785495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14269381222017610850094653 5351017958256604068785495)
                ·
                  refine ⟨8026526937384906103178243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5351017958256604068785495 8026526937384906103178243)
                  ·
                    refine ⟨12039790406077359154767365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8026526937384906103178243 12039790406077359154767365)
                    ·
                      refine ⟨2257460701139504841518881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12039790406077359154767365 2257460701139504841518881)
                      ·
                        rfl

theorem cell23_4396389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_4396389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396389 prefixEnd_4396389 := by exact prefixLift 4396389
  have htrace : WordTrace (prefixWord ++ tailWord_4396389) baseStart_4396389 baseEnd_4396389 := by
    simpa [prefixWord, tailWord_4396389, baseEnd_4396389] using wordTrace_append hprefix tailTrace_4396389
  have hstable : (prefixWord ++ tailWord_4396389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396389).length < 2 ^ (prefixWord ++ tailWord_4396389).sum := by decide
  have hdescent : baseEnd_4396389 < baseStart_4396389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396402 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_4396402 : Nat := 118140960795 + 4396402 * 2 ^ 59
def prefixEnd_4396402 : Nat := 4983230072969 + 3 ^ 40 * 4396402 * 2
def baseEnd_4396402 : Nat := 2257467376388013290656321

theorem tailTrace_4396402 : CollatzResearch.WordTrace tailWord_4396402 prefixEnd_4396402 2257467376388013290656321 := by
  unfold tailWord_4396402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40087488554648468632207865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106899969479062583019220973 40087488554648468632207865)
  ·
    refine ⟨30065616415986351474155899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40087488554648468632207865 30065616415986351474155899)
    ·
      refine ⟨45098424623979527211233849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30065616415986351474155899 45098424623979527211233849)
      ·
        refine ⟨33823818467984645408425387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45098424623979527211233849 33823818467984645408425387)
        ·
          refine ⟨50735727701976968112638081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33823818467984645408425387 50735727701976968112638081)
          ·
            refine ⟨38051795776482726084478561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50735727701976968112638081 38051795776482726084478561)
            ·
              refine ⟨28538846832362044563358921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38051795776482726084478561 28538846832362044563358921)
              ·
                refine ⟨21404135124271533422519191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28538846832362044563358921 21404135124271533422519191)
                ·
                  refine ⟨32106202686407300133778787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21404135124271533422519191 32106202686407300133778787)
                  ·
                    refine ⟨48159304029610950200668181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32106202686407300133778787 48159304029610950200668181)
                    ·
                      refine ⟨2257467376388013290656321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48159304029610950200668181 2257467376388013290656321)
                      ·
                        rfl

theorem cell23_4396402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_4396402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396402 prefixEnd_4396402 := by exact prefixLift 4396402
  have htrace : WordTrace (prefixWord ++ tailWord_4396402) baseStart_4396402 baseEnd_4396402 := by
    simpa [prefixWord, tailWord_4396402, baseEnd_4396402] using wordTrace_append hprefix tailTrace_4396402
  have hstable : (prefixWord ++ tailWord_4396402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396402).length < 2 ^ (prefixWord ++ tailWord_4396402).sum := by decide
  have hdescent : baseEnd_4396402 < baseStart_4396402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396419 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 4]
def baseStart_4396419 : Nat := 118140960795 + 4396419 * 2 ^ 59
def prefixEnd_4396419 : Nat := 4983230072969 + 3 ^ 40 * 4396419 * 2
def baseEnd_4396419 : Nat := 2257476105559139724143743

theorem tailTrace_4396419 : CollatzResearch.WordTrace tailWord_4396419 prefixEnd_4396419 2257476105559139724143743 := by
  unfold tailWord_4396419
  simp only [CollatzResearch.WordTrace]
  refine ⟨160350574259532286432200311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106900382839688190954800207 160350574259532286432200311)
  ·
    refine ⟨240525861389298429648300467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160350574259532286432200311 240525861389298429648300467)
    ·
      refine ⟨360788792083947644472450701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240525861389298429648300467 360788792083947644472450701)
      ·
        refine ⟨135295797031480366677169013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360788792083947644472450701 135295797031480366677169013)
        ·
          refine ⟨12683980971701284375984595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135295797031480366677169013 12683980971701284375984595)
          ·
            refine ⟨19025971457551926563976893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12683980971701284375984595 19025971457551926563976893)
            ·
              refine ⟨7134739296581972461491335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19025971457551926563976893 7134739296581972461491335)
              ·
                refine ⟨10702108944872958692237003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7134739296581972461491335 10702108944872958692237003)
                ·
                  refine ⟨16053163417309438038355505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10702108944872958692237003 16053163417309438038355505)
                  ·
                    refine ⟨12039872562982078528766629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16053163417309438038355505 12039872562982078528766629)
                    ·
                      refine ⟨2257476105559139724143743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12039872562982078528766629 2257476105559139724143743)
                      ·
                        rfl

theorem cell23_4396419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_4396419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396419 prefixEnd_4396419 := by exact prefixLift 4396419
  have htrace : WordTrace (prefixWord ++ tailWord_4396419) baseStart_4396419 baseEnd_4396419 := by
    simpa [prefixWord, tailWord_4396419, baseEnd_4396419] using wordTrace_append hprefix tailTrace_4396419
  have hstable : (prefixWord ++ tailWord_4396419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396419).length < 2 ^ (prefixWord ++ tailWord_4396419).sum := by decide
  have hdescent : baseEnd_4396419 < baseStart_4396419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396434 : List Nat := [3, 2, 3, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4396434 : Nat := 118140960795 + 4396434 * 2 ^ 59
def prefixEnd_4396434 : Nat := 4983230072969 + 3 ^ 40 * 4396434 * 2
def baseEnd_4396434 : Nat := 2257483807768957165456175

theorem tailTrace_4396434 : CollatzResearch.WordTrace tailWord_4396434 prefixEnd_4396434 2257483807768957165456175 := by
  unfold tailWord_4396434
  simp only [CollatzResearch.WordTrace]
  refine ⟨40087780338619485998499089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106900747569651962662664237 40087780338619485998499089)
  ·
    refine ⟨30065835253964614498874317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40087780338619485998499089 30065835253964614498874317)
    ·
      refine ⟨11274688220236730437077869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30065835253964614498874317 11274688220236730437077869)
      ·
        refine ⟨4228008082588773913904201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11274688220236730437077869 4228008082588773913904201)
        ·
          refine ⟨3171006061941580435428151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4228008082588773913904201 3171006061941580435428151)
          ·
            refine ⟨4756509092912370653142227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171006061941580435428151 4756509092912370653142227)
            ·
              refine ⟨7134763639368555979713341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756509092912370653142227 7134763639368555979713341)
              ·
                refine ⟨2675536364763208492392503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7134763639368555979713341 2675536364763208492392503)
                ·
                  refine ⟨4013304547144812738588755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675536364763208492392503 4013304547144812738588755)
                  ·
                    refine ⟨6019956820717219107883133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4013304547144812738588755 6019956820717219107883133)
                    ·
                      refine ⟨2257483807768957165456175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6019956820717219107883133 2257483807768957165456175)
                      ·
                        rfl

theorem cell23_4396434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4396434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396434 prefixEnd_4396434 := by exact prefixLift 4396434
  have htrace : WordTrace (prefixWord ++ tailWord_4396434) baseStart_4396434 baseEnd_4396434 := by
    simpa [prefixWord, tailWord_4396434, baseEnd_4396434] using wordTrace_append hprefix tailTrace_4396434
  have hstable : (prefixWord ++ tailWord_4396434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396434).length < 2 ^ (prefixWord ++ tailWord_4396434).sum := by decide
  have hdescent : baseEnd_4396434 < baseStart_4396434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396446 : List Nat := [4, 3, 1, 2, 2, 2, 9]
def baseStart_4396446 : Nat := 118140960795 + 4396446 * 2 ^ 59
def prefixEnd_4396446 : Nat := 4983230072969 + 3 ^ 40 * 4396446 * 2
def baseEnd_4396446 : Nat := 27870246537491495290199

theorem tailTrace_4396446 : CollatzResearch.WordTrace tailWord_4396446 prefixEnd_4396446 27870246537491495290199 := by
  unfold tailWord_4396446
  simp only [CollatzResearch.WordTrace]
  refine ⟨20043944878804308755429149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106901039353622980028955461 20043944878804308755429149)
  ·
    refine ⟨7516479329551615783285931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20043944878804308755429149 7516479329551615783285931)
    ·
      refine ⟨11274718994327423674928897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7516479329551615783285931 11274718994327423674928897)
      ·
        refine ⟨8456039245745567756196673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11274718994327423674928897 8456039245745567756196673)
        ·
          refine ⟨6342029434309175817147505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8456039245745567756196673 6342029434309175817147505)
          ·
            refine ⟨4756522075731881862860629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6342029434309175817147505 4756522075731881862860629)
            ·
              refine ⟨27870246537491495290199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4756522075731881862860629 27870246537491495290199)
              ·
                rfl

theorem cell23_4396446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 9].length) (baseStart_4396446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396446 prefixEnd_4396446 := by exact prefixLift 4396446
  have htrace : WordTrace (prefixWord ++ tailWord_4396446) baseStart_4396446 baseEnd_4396446 := by
    simpa [prefixWord, tailWord_4396446, baseEnd_4396446] using wordTrace_append hprefix tailTrace_4396446
  have hstable : (prefixWord ++ tailWord_4396446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396446).length < 2 ^ (prefixWord ++ tailWord_4396446).sum := by decide
  have hdescent : baseEnd_4396446 < baseStart_4396446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396452 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_4396452 : Nat := 118140960795 + 4396452 * 2 ^ 59
def prefixEnd_4396452 : Nat := 4983230072969 + 3 ^ 40 * 4396452 * 2
def baseEnd_4396452 : Nat := 2257493050420738095031091

theorem tailTrace_4396452 : CollatzResearch.WordTrace tailWord_4396452 prefixEnd_4396452 2257493050420738095031091 := by
  unfold tailWord_4396452
  simp only [CollatzResearch.WordTrace]
  refine ⟨80175888934206366534075805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106901185245608488712101073 80175888934206366534075805)
  ·
    refine ⟨30065958350327387450278427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80175888934206366534075805 30065958350327387450278427)
    ·
      refine ⟨45098937525491081175417641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30065958350327387450278427 45098937525491081175417641)
      ·
        refine ⟨33824203144118310881563231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45098937525491081175417641 33824203144118310881563231)
        ·
          refine ⟨50736304716177466322344847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33824203144118310881563231 50736304716177466322344847)
          ·
            refine ⟨76104457074266199483517271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50736304716177466322344847 76104457074266199483517271)
            ·
              refine ⟨114156685611399299225275907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76104457074266199483517271 114156685611399299225275907)
              ·
                refine ⟨171235028417098948837913861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114156685611399299225275907 171235028417098948837913861)
                ·
                  refine ⟨32106567828206052907108849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171235028417098948837913861 32106567828206052907108849)
                  ·
                    refine ⟨24079925871154539680331637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32106567828206052907108849 24079925871154539680331637)
                    ·
                      refine ⟨2257493050420738095031091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24079925871154539680331637 2257493050420738095031091)
                      ·
                        rfl

theorem cell23_4396452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_4396452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396452 prefixEnd_4396452 := by exact prefixLift 4396452
  have htrace : WordTrace (prefixWord ++ tailWord_4396452) baseStart_4396452 baseEnd_4396452 := by
    simpa [prefixWord, tailWord_4396452, baseEnd_4396452] using wordTrace_append hprefix tailTrace_4396452
  have hstable : (prefixWord ++ tailWord_4396452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396452).length < 2 ^ (prefixWord ++ tailWord_4396452).sum := by decide
  have hdescent : baseEnd_4396452 < baseStart_4396452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396472 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 2, 6]
def baseStart_4396472 : Nat := 118140960795 + 4396472 * 2 ^ 59
def prefixEnd_4396472 : Nat := 4983230072969 + 3 ^ 40 * 4396472 * 2
def baseEnd_4396472 : Nat := 752501106677942672260333

theorem tailTrace_4396472 : CollatzResearch.WordTrace tailWord_4396472 prefixEnd_4396472 752501106677942672260333 := by
  unfold tailWord_4396472
  simp only [CollatzResearch.WordTrace]
  refine ⟨80176253664170138241939835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106901671552226850989253113 80176253664170138241939835)
  ·
    refine ⟨120264380496255207362909753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80176253664170138241939835 120264380496255207362909753)
    ·
      refine ⟨90198285372191405522182315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120264380496255207362909753 90198285372191405522182315)
      ·
        refine ⟨135297428058287108283273473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90198285372191405522182315 135297428058287108283273473)
        ·
          refine ⟨101473071043715331212455105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135297428058287108283273473 101473071043715331212455105)
          ·
            refine ⟨76104803282786498409341329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101473071043715331212455105 76104803282786498409341329)
            ·
              refine ⟨57078602462089873807005997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76104803282786498409341329 57078602462089873807005997)
              ·
                refine ⟨21404475923283702677627249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57078602462089873807005997 21404475923283702677627249)
                ·
                  refine ⟨16053356942462777008220437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21404475923283702677627249 16053356942462777008220437)
                  ·
                    refine ⟨752501106677942672260333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16053356942462777008220437 752501106677942672260333)
                    ·
                      rfl

theorem cell23_4396472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_4396472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396472 prefixEnd_4396472 := by exact prefixLift 4396472
  have htrace : WordTrace (prefixWord ++ tailWord_4396472) baseStart_4396472 baseEnd_4396472 := by
    simpa [prefixWord, tailWord_4396472, baseEnd_4396472] using wordTrace_append hprefix tailTrace_4396472
  have hstable : (prefixWord ++ tailWord_4396472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396472).length < 2 ^ (prefixWord ++ tailWord_4396472).sum := by decide
  have hdescent : baseEnd_4396472 < baseStart_4396472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396473 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 3]
def baseStart_4396473 : Nat := 118140960795 + 4396473 * 2 ^ 59
def prefixEnd_4396473 : Nat := 4983230072969 + 3 ^ 40 * 4396473 * 2
def baseEnd_4396473 : Nat := 2257503833514482512868495

theorem tailTrace_4396473 : CollatzResearch.WordTrace tailWord_4396473 prefixEnd_4396473 2257503833514482512868495 := by
  unfold tailWord_4396473
  simp only [CollatzResearch.WordTrace]
  refine ⟨160352543801336653654666073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106901695867557769103110715 160352543801336653654666073)
  ·
    refine ⟨120264407851002490240999555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160352543801336653654666073 120264407851002490240999555)
    ·
      refine ⟨180396611776503735361499333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120264407851002490240999555 180396611776503735361499333)
      ·
        refine ⟨33824364708094450380281125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180396611776503735361499333 33824364708094450380281125)
        ·
          refine ⟨6342068382767709446302711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33824364708094450380281125 6342068382767709446302711)
          ·
            refine ⟨9513102574151564169454067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6342068382767709446302711 9513102574151564169454067)
            ·
              refine ⟨14269653861227346254181101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9513102574151564169454067 14269653861227346254181101)
              ·
                refine ⟨5351120197960254845317913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14269653861227346254181101 5351120197960254845317913)
                ·
                  refine ⟨4013340148470191133988435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5351120197960254845317913 4013340148470191133988435)
                  ·
                    refine ⟨6020010222705286700982653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4013340148470191133988435 6020010222705286700982653)
                    ·
                      refine ⟨2257503833514482512868495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6020010222705286700982653 2257503833514482512868495)
                      ·
                        rfl

theorem cell23_4396473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_4396473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396473 prefixEnd_4396473 := by exact prefixLift 4396473
  have htrace : WordTrace (prefixWord ++ tailWord_4396473) baseStart_4396473 baseEnd_4396473 := by
    simpa [prefixWord, tailWord_4396473, baseEnd_4396473] using wordTrace_append hprefix tailTrace_4396473
  have hstable : (prefixWord ++ tailWord_4396473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396473).length < 2 ^ (prefixWord ++ tailWord_4396473).sum := by decide
  have hdescent : baseEnd_4396473 < baseStart_4396473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396479 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 5, 4, 2]
def baseStart_4396479 : Nat := 118140960795 + 4396479 * 2 ^ 59
def prefixEnd_4396479 : Nat := 4983230072969 + 3 ^ 40 * 4396479 * 2
def baseEnd_4396479 : Nat := 2257506914398409489393467

theorem tailTrace_4396479 : CollatzResearch.WordTrace tailWord_4396479 prefixEnd_4396479 2257506914398409489393467 := by
  unfold tailWord_4396479
  simp only [CollatzResearch.WordTrace]
  refine ⟨160352762639314916679384491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106901841759543277786256327 160352762639314916679384491)
  ·
    refine ⟨240529143958972375019076737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160352762639314916679384491 240529143958972375019076737)
    ·
      refine ⟨180396857969229281264307553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240529143958972375019076737 180396857969229281264307553)
      ·
        refine ⟨135297643476921960948230665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180396857969229281264307553 135297643476921960948230665)
        ·
          refine ⟨101473232607691470711172999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135297643476921960948230665 101473232607691470711172999)
          ·
            refine ⟨152209848911537206066759499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101473232607691470711172999 152209848911537206066759499)
            ·
              refine ⟨228314773367305809100139249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152209848911537206066759499 228314773367305809100139249)
              ·
                refine ⟨171236080025479356825104437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228314773367305809100139249 171236080025479356825104437)
                ·
                  refine ⟨16053382502388689702353541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171236080025479356825104437 16053382502388689702353541)
                  ·
                    refine ⟨3010009219197879319191289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16053382502388689702353541 3010009219197879319191289)
                    ·
                      refine ⟨2257506914398409489393467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010009219197879319191289 2257506914398409489393467)
                      ·
                        rfl

theorem cell23_4396479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_4396479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396479 prefixEnd_4396479 := by exact prefixLift 4396479
  have htrace : WordTrace (prefixWord ++ tailWord_4396479) baseStart_4396479 baseEnd_4396479 := by
    simpa [prefixWord, tailWord_4396479, baseEnd_4396479] using wordTrace_append hprefix tailTrace_4396479
  have hstable : (prefixWord ++ tailWord_4396479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396479).length < 2 ^ (prefixWord ++ tailWord_4396479).sum := by decide
  have hdescent : baseEnd_4396479 < baseStart_4396479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396513 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_4396513 : Nat := 118140960795 + 4396513 * 2 ^ 59
def prefixEnd_4396513 : Nat := 4983230072969 + 3 ^ 40 * 4396513 * 2
def baseEnd_4396513 : Nat := 2257524372740662356368311

theorem tailTrace_4396513 : CollatzResearch.WordTrace tailWord_4396513 prefixEnd_4396513 2257524372740662356368311 := by
  unfold tailWord_4396513
  simp only [CollatzResearch.WordTrace]
  refine ⟨160354002721191740486122193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106902668480794493657414795 160354002721191740486122193)
  ·
    refine ⟨120265502040893805364591645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160354002721191740486122193 120265502040893805364591645)
    ·
      refine ⟨45099563265335177011721867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120265502040893805364591645 45099563265335177011721867)
      ·
        refine ⟨67649344898002765517582801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45099563265335177011721867 67649344898002765517582801)
        ·
          refine ⟨50737008673502074138187101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67649344898002765517582801 50737008673502074138187101)
          ·
            refine ⟨19026378252563277801820163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50737008673502074138187101 19026378252563277801820163)
            ·
              refine ⟨28539567378844916702730245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19026378252563277801820163 28539567378844916702730245)
              ·
                refine ⟨5351168883533421881761921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28539567378844916702730245 5351168883533421881761921)
                ·
                  refine ⟨4013376662650066411321441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5351168883533421881761921 4013376662650066411321441)
                  ·
                    refine ⟨3010032496987549808491081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4013376662650066411321441 3010032496987549808491081)
                    ·
                      refine ⟨2257524372740662356368311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010032496987549808491081 2257524372740662356368311)
                      ·
                        rfl

theorem cell23_4396513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_4396513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396513 prefixEnd_4396513 := by exact prefixLift 4396513
  have htrace : WordTrace (prefixWord ++ tailWord_4396513) baseStart_4396513 baseEnd_4396513 := by
    simpa [prefixWord, tailWord_4396513, baseEnd_4396513] using wordTrace_append hprefix tailTrace_4396513
  have hstable : (prefixWord ++ tailWord_4396513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396513).length < 2 ^ (prefixWord ++ tailWord_4396513).sum := by decide
  have hdescent : baseEnd_4396513 < baseStart_4396513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396529 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_4396529 : Nat := 118140960795 + 4396529 * 2 ^ 59
def prefixEnd_4396529 : Nat := 4983230072969 + 3 ^ 40 * 4396529 * 2
def baseEnd_4396529 : Nat := 2257532588431134293768237

theorem tailTrace_4396529 : CollatzResearch.WordTrace tailWord_4396529 prefixEnd_4396529 2257532588431134293768237 := by
  unfold tailWord_4396529
  simp only [CollatzResearch.WordTrace]
  refine ⟨160354586289133775218704641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106903057526089183479136427 160354586289133775218704641)
  ·
    refine ⟨120265939716850331414028481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160354586289133775218704641 120265939716850331414028481)
    ·
      refine ⟨90199454787637748560521361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120265939716850331414028481 90199454787637748560521361)
      ·
        refine ⟨67649591090728311420391021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90199454787637748560521361 67649591090728311420391021)
        ·
          refine ⟨25368596659023116782646633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67649591090728311420391021 25368596659023116782646633)
          ·
            refine ⟨19026447494267337586984975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25368596659023116782646633 19026447494267337586984975)
            ·
              refine ⟨28539671241401006380477463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19026447494267337586984975 28539671241401006380477463)
              ·
                refine ⟨42809506862101509570716195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28539671241401006380477463 42809506862101509570716195)
                ·
                  refine ⟨64214260293152264356074293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42809506862101509570716195 64214260293152264356074293)
                  ·
                    refine ⟨6020086902483024783381965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64214260293152264356074293 6020086902483024783381965)
                    ·
                      refine ⟨2257532588431134293768237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6020086902483024783381965 2257532588431134293768237)
                      ·
                        rfl

theorem cell23_4396529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_4396529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396529 prefixEnd_4396529 := by exact prefixLift 4396529
  have htrace : WordTrace (prefixWord ++ tailWord_4396529) baseStart_4396529 baseEnd_4396529 := by
    simpa [prefixWord, tailWord_4396529, baseEnd_4396529] using wordTrace_append hprefix tailTrace_4396529
  have hstable : (prefixWord ++ tailWord_4396529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396529).length < 2 ^ (prefixWord ++ tailWord_4396529).sum := by decide
  have hdescent : baseEnd_4396529 < baseStart_4396529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396530 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4396530 : Nat := 118140960795 + 4396530 * 2 ^ 59
def prefixEnd_4396530 : Nat := 4983230072969 + 3 ^ 40 * 4396530 * 2
def baseEnd_4396530 : Nat := 2257533101911788789855733

theorem tailTrace_4396530 : CollatzResearch.WordTrace tailWord_4396530 prefixEnd_4396530 2257533101911788789855733 := by
  unfold tailWord_4396530
  simp only [CollatzResearch.WordTrace]
  refine ⟨40088655690532538097372761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106903081841420101592994029 40088655690532538097372761)
  ·
    refine ⟨30066491767899403573029571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40088655690532538097372761 30066491767899403573029571)
    ·
      refine ⟨45099737651849105359544357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30066491767899403573029571 45099737651849105359544357)
      ·
        refine ⟨8456200809721707254914567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45099737651849105359544357 8456200809721707254914567)
        ·
          refine ⟨12684301214582560882371851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8456200809721707254914567 12684301214582560882371851)
          ·
            refine ⟨19026451821873841323557777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12684301214582560882371851 19026451821873841323557777)
            ·
              refine ⟨14269838866405380992668333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19026451821873841323557777 14269838866405380992668333)
              ·
                refine ⟨5351189574902017872250625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14269838866405380992668333 5351189574902017872250625)
                ·
                  refine ⟨4013392181176513404187969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5351189574902017872250625 4013392181176513404187969)
                  ·
                    refine ⟨3010044135882385053140977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4013392181176513404187969 3010044135882385053140977)
                    ·
                      refine ⟨2257533101911788789855733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010044135882385053140977 2257533101911788789855733)
                      ·
                        rfl

theorem cell23_4396530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4396530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396530 prefixEnd_4396530 := by exact prefixLift 4396530
  have htrace : WordTrace (prefixWord ++ tailWord_4396530) baseStart_4396530 baseEnd_4396530 := by
    simpa [prefixWord, tailWord_4396530, baseEnd_4396530] using wordTrace_append hprefix tailTrace_4396530
  have hstable : (prefixWord ++ tailWord_4396530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396530).length < 2 ^ (prefixWord ++ tailWord_4396530).sum := by decide
  have hdescent : baseEnd_4396530 < baseStart_4396530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396564 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4396564 : Nat := 118140960795 + 4396564 * 2 ^ 59
def prefixEnd_4396564 : Nat := 4983230072969 + 3 ^ 40 * 4396564 * 2
def baseEnd_4396564 : Nat := 2257550560254041656830577

theorem tailTrace_4396564 : CollatzResearch.WordTrace tailWord_4396564 prefixEnd_4396564 2257550560254041656830577 := by
  unfold tailWord_4396564
  simp only [CollatzResearch.WordTrace]
  refine ⟨80177931422003488098114373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106903908562671317464152497 80177931422003488098114373)
  ·
    refine ⟨15033362141625654018396445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80177931422003488098114373 15033362141625654018396445)
    ·
      refine ⟨5637510803109620256898667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15033362141625654018396445 5637510803109620256898667)
      ·
        refine ⟨8456266204664430385348001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5637510803109620256898667 8456266204664430385348001)
        ·
          refine ⟨6342199653498322789011001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8456266204664430385348001 6342199653498322789011001)
          ·
            refine ⟨4756649740123742091758251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6342199653498322789011001 4756649740123742091758251)
            ·
              refine ⟨7134974610185613137637377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756649740123742091758251 7134974610185613137637377)
              ·
                refine ⟨5351230957639209853228033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7134974610185613137637377 5351230957639209853228033)
                ·
                  refine ⟨4013423218229407389921025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5351230957639209853228033 4013423218229407389921025)
                  ·
                    refine ⟨3010067413672055542440769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4013423218229407389921025 3010067413672055542440769)
                    ·
                      refine ⟨2257550560254041656830577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010067413672055542440769 2257550560254041656830577)
                      ·
                        rfl

theorem cell23_4396564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4396564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396564 prefixEnd_4396564 := by exact prefixLift 4396564
  have htrace : WordTrace (prefixWord ++ tailWord_4396564) baseStart_4396564 baseEnd_4396564 := by
    simpa [prefixWord, tailWord_4396564, baseEnd_4396564] using wordTrace_append hprefix tailTrace_4396564
  have hstable : (prefixWord ++ tailWord_4396564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396564).length < 2 ^ (prefixWord ++ tailWord_4396564).sum := by decide
  have hdescent : baseEnd_4396564 < baseStart_4396564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396609 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 10]
def baseStart_4396609 : Nat := 118140960795 + 4396609 * 2 ^ 59
def prefixEnd_4396609 : Nat := 4983230072969 + 3 ^ 40 * 4396609 * 2
def baseEnd_4396609 : Nat := 250841518542610442307541

theorem tailTrace_4396609 : CollatzResearch.WordTrace tailWord_4396609 prefixEnd_4396609 250841518542610442307541 := by
  unfold tailWord_4396609
  simp only [CollatzResearch.WordTrace]
  refine ⟨160357504128843948881616881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106905002752562632587744587 160357504128843948881616881)
  ·
    refine ⟨120268128096632961661212661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160357504128843948881616881 120268128096632961661212661)
    ·
      refine ⟨11275137009059340155738687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120268128096632961661212661 11275137009059340155738687)
      ·
        refine ⟨16912705513589010233608031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11275137009059340155738687 16912705513589010233608031)
        ·
          refine ⟨25369058270383515350412047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16912705513589010233608031 25369058270383515350412047)
          ·
            refine ⟨38053587405575273025618071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25369058270383515350412047 38053587405575273025618071)
            ·
              refine ⟨57080381108362909538427107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38053587405575273025618071 57080381108362909538427107)
              ·
                refine ⟨85620571662544364307640661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57080381108362909538427107 85620571662544364307640661)
                ·
                  refine ⟨250841518542610442307541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85620571662544364307640661 250841518542610442307541)
                  ·
                    rfl

theorem cell23_4396609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 10].length) (baseStart_4396609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396609 prefixEnd_4396609 := by exact prefixLift 4396609
  have htrace : WordTrace (prefixWord ++ tailWord_4396609) baseStart_4396609 baseEnd_4396609 := by
    simpa [prefixWord, tailWord_4396609, baseEnd_4396609] using wordTrace_append hprefix tailTrace_4396609
  have hstable : (prefixWord ++ tailWord_4396609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396609).length < 2 ^ (prefixWord ++ tailWord_4396609).sum := by decide
  have hdescent : baseEnd_4396609 < baseStart_4396609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396643 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 6]
def baseStart_4396643 : Nat := 118140960795 + 4396643 * 2 ^ 59
def prefixEnd_4396643 : Nat := 4983230072969 + 3 ^ 40 * 4396643 * 2
def baseEnd_4396643 : Nat := 250843458358416316415857

theorem tailTrace_4396643 : CollatzResearch.WordTrace tailWord_4396643 prefixEnd_4396643 250843458358416316415857 := by
  unfold tailWord_4396643
  simp only [CollatzResearch.WordTrace]
  refine ⟨160358744210720772688354583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106905829473813848458903055 160358744210720772688354583)
  ·
    refine ⟨240538116316081159032531875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160358744210720772688354583 240538116316081159032531875)
    ·
      refine ⟨360807174474121738548797813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240538116316081159032531875 360807174474121738548797813)
      ·
        refine ⟨33825672606948912988949795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 360807174474121738548797813 33825672606948912988949795)
        ·
          refine ⟨50738508910423369483424693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33825672606948912988949795 50738508910423369483424693)
          ·
            refine ⟨4756735210352190889071065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50738508910423369483424693 4756735210352190889071065)
            ·
              refine ⟨3567551407764143166803299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4756735210352190889071065 3567551407764143166803299)
              ·
                refine ⟨5351327111646214750204949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567551407764143166803299 5351327111646214750204949)
                ·
                  refine ⟨250843458358416316415857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5351327111646214750204949 250843458358416316415857)
                  ·
                    rfl

theorem cell23_4396643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 6].length) (baseStart_4396643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396643 prefixEnd_4396643 := by exact prefixLift 4396643
  have htrace : WordTrace (prefixWord ++ tailWord_4396643) baseStart_4396643 baseEnd_4396643 := by
    simpa [prefixWord, tailWord_4396643, baseEnd_4396643] using wordTrace_append hprefix tailTrace_4396643
  have hstable : (prefixWord ++ tailWord_4396643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396643).length < 2 ^ (prefixWord ++ tailWord_4396643).sum := by decide
  have hdescent : baseEnd_4396643 < baseStart_4396643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396656 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 3, 5]
def baseStart_4396656 : Nat := 118140960795 + 4396656 * 2 ^ 59
def prefixEnd_4396656 : Nat := 4983230072969 + 3 ^ 40 * 4396656 * 2
def baseEnd_4396656 : Nat := 752532600158085098960051

theorem tailTrace_4396656 : CollatzResearch.WordTrace tailWord_4396656 prefixEnd_4396656 752532600158085098960051 := by
  unfold tailWord_4396656
  simp only [CollatzResearch.WordTrace]
  refine ⟨80179609179836837954288911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106906145573115783939051881 80179609179836837954288911)
  ·
    refine ⟨120269413769755256931433367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80179609179836837954288911 120269413769755256931433367)
    ·
      refine ⟨180404120654632885397150051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120269413769755256931433367 180404120654632885397150051)
      ·
        refine ⟨270606180981949328095725077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180404120654632885397150051 270606180981949328095725077)
        ·
          refine ⟨12684664733528874754487113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 270606180981949328095725077 12684664733528874754487113)
          ·
            refine ⟨9513498550146656065865335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12684664733528874754487113 9513498550146656065865335)
            ·
              refine ⟨14270247825219984098798003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9513498550146656065865335 14270247825219984098798003)
              ·
                refine ⟨21405371737829976148197005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14270247825219984098798003 21405371737829976148197005)
                ·
                  refine ⟨8027014401686241055573877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21405371737829976148197005 8027014401686241055573877)
                  ·
                    refine ⟨752532600158085098960051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8027014401686241055573877 752532600158085098960051)
                    ·
                      rfl

theorem cell23_4396656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_4396656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396656 prefixEnd_4396656 := by exact prefixLift 4396656
  have htrace : WordTrace (prefixWord ++ tailWord_4396656) baseStart_4396656 baseEnd_4396656 := by
    simpa [prefixWord, tailWord_4396656, baseEnd_4396656] using wordTrace_append hprefix tailTrace_4396656
  have hstable : (prefixWord ++ tailWord_4396656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396656).length < 2 ^ (prefixWord ++ tailWord_4396656).sum := by decide
  have hdescent : baseEnd_4396656 < baseStart_4396656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396689 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_4396689 : Nat := 118140960795 + 4396689 * 2 ^ 59
def prefixEnd_4396689 : Nat := 4983230072969 + 3 ^ 40 * 4396689 * 2
def baseEnd_4396689 : Nat := 2257614745335853667767501

theorem tailTrace_4396689 : CollatzResearch.WordTrace tailWord_4396689 prefixEnd_4396689 2257614745335853667767501 := by
  unfold tailWord_4396689
  simp only [CollatzResearch.WordTrace]
  refine ⟨160360421968554122544529121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106906947979036081696352747 160360421968554122544529121)
  ·
    refine ⟨120270316476415591908396841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160360421968554122544529121 120270316476415591908396841)
    ·
      refine ⟨90202737357311693931297631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120270316476415591908396841 90202737357311693931297631)
      ·
        refine ⟨135304106035967540896946447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90202737357311693931297631 135304106035967540896946447)
        ·
          refine ⟨202956159053951311345419671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135304106035967540896946447 202956159053951311345419671)
          ·
            refine ⟨304434238580926967018129507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202956159053951311345419671 304434238580926967018129507)
            ·
              refine ⟨456651357871390450527194261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304434238580926967018129507 456651357871390450527194261)
              ·
                refine ⟨21405532400221427368462231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456651357871390450527194261 21405532400221427368462231)
                ·
                  refine ⟨32108298600332141052693347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21405532400221427368462231 32108298600332141052693347)
                  ·
                    refine ⟨48162447900498211579040021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32108298600332141052693347 48162447900498211579040021)
                    ·
                      refine ⟨2257614745335853667767501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48162447900498211579040021 2257614745335853667767501)
                      ·
                        rfl

theorem cell23_4396689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_4396689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396689 prefixEnd_4396689 := by exact prefixLift 4396689
  have htrace : WordTrace (prefixWord ++ tailWord_4396689) baseStart_4396689 baseEnd_4396689 := by
    simpa [prefixWord, tailWord_4396689, baseEnd_4396689] using wordTrace_append hprefix tailTrace_4396689
  have hstable : (prefixWord ++ tailWord_4396689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396689).length < 2 ^ (prefixWord ++ tailWord_4396689).sum := by decide
  have hdescent : baseEnd_4396689 < baseStart_4396689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396693 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_4396693 : Nat := 118140960795 + 4396693 * 2 ^ 59
def prefixEnd_4396693 : Nat := 4983230072969 + 3 ^ 40 * 4396693 * 2
def baseEnd_4396693 : Nat := 2257616799258471652117483

theorem tailTrace_4396693 : CollatzResearch.WordTrace tailWord_4396693 prefixEnd_4396693 2257616799258471652117483 := by
  unfold tailWord_4396693
  simp only [CollatzResearch.WordTrace]
  refine ⟨160360567860539631227674733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106907045240359754151783155 160360567860539631227674733)
  ·
    refine ⟨60135212947702361710378025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160360567860539631227674733 60135212947702361710378025)
    ·
      refine ⟨45101409710776771282783519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60135212947702361710378025 45101409710776771282783519)
      ·
        refine ⟨67652114566165156924175279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45101409710776771282783519 67652114566165156924175279)
        ·
          refine ⟨101478171849247735386262919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67652114566165156924175279 101478171849247735386262919)
          ·
            refine ⟨152217257773871603079394379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101478171849247735386262919 152217257773871603079394379)
            ·
              refine ⟨228325886660807404619091569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152217257773871603079394379 228325886660807404619091569)
              ·
                refine ⟨171244414995605553464318677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228325886660807404619091569 171244414995605553464318677)
                ·
                  refine ⟨4013540976459505159319969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 171244414995605553464318677 4013540976459505159319969)
                  ·
                    refine ⟨3010155732344628869489977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4013540976459505159319969 3010155732344628869489977)
                    ·
                      refine ⟨2257616799258471652117483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010155732344628869489977 2257616799258471652117483)
                      ·
                        rfl

theorem cell23_4396693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_4396693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396693 prefixEnd_4396693 := by exact prefixLift 4396693
  have htrace : WordTrace (prefixWord ++ tailWord_4396693) baseStart_4396693 baseEnd_4396693 := by
    simpa [prefixWord, tailWord_4396693, baseEnd_4396693] using wordTrace_append hprefix tailTrace_4396693
  have hstable : (prefixWord ++ tailWord_4396693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396693).length < 2 ^ (prefixWord ++ tailWord_4396693).sum := by decide
  have hdescent : baseEnd_4396693 < baseStart_4396693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396727 : List Nat := [1, 1, 3, 1, 5, 1, 1, 5, 1, 2, 2]
def baseStart_4396727 : Nat := 118140960795 + 4396727 * 2 ^ 59
def prefixEnd_4396727 : Nat := 4983230072969 + 3 ^ 40 * 4396727 * 2
def baseEnd_4396727 : Nat := 2257634257600724519092327

theorem tailTrace_4396727 : CollatzResearch.WordTrace tailWord_4396727 prefixEnd_4396727 2257634257600724519092327 := by
  unfold tailWord_4396727
  simp only [CollatzResearch.WordTrace]
  refine ⟨160361807942416455034412435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106907871961610970022941623 160361807942416455034412435)
  ·
    refine ⟨240542711913624682551618653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160361807942416455034412435 240542711913624682551618653)
    ·
      refine ⟨90203516967609255956856995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240542711913624682551618653 90203516967609255956856995)
      ·
        refine ⟨135305275451413883935285493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90203516967609255956856995 135305275451413883935285493)
        ·
          refine ⟨12684869573570051618933015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135305275451413883935285493 12684869573570051618933015)
          ·
            refine ⟨19027304360355077428399523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12684869573570051618933015 19027304360355077428399523)
            ·
              refine ⟨28540956540532616142599285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19027304360355077428399523 28540956540532616142599285)
              ·
                refine ⟨2675714675674932763368683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28540956540532616142599285 2675714675674932763368683)
                ·
                  refine ⟨4013572013512399145053025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675714675674932763368683 4013572013512399145053025)
                  ·
                    refine ⟨3010179010134299358789769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4013572013512399145053025 3010179010134299358789769)
                    ·
                      refine ⟨2257634257600724519092327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010179010134299358789769 2257634257600724519092327)
                      ·
                        rfl

theorem cell23_4396727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_4396727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396727 prefixEnd_4396727 := by exact prefixLift 4396727
  have htrace : WordTrace (prefixWord ++ tailWord_4396727) baseStart_4396727 baseEnd_4396727 := by
    simpa [prefixWord, tailWord_4396727, baseEnd_4396727] using wordTrace_append hprefix tailTrace_4396727
  have hstable : (prefixWord ++ tailWord_4396727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396727).length < 2 ^ (prefixWord ++ tailWord_4396727).sum := by decide
  have hdescent : baseEnd_4396727 < baseStart_4396727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396730 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3]
def baseStart_4396730 : Nat := 118140960795 + 4396730 * 2 ^ 59
def prefixEnd_4396730 : Nat := 4983230072969 + 3 ^ 40 * 4396730 * 2
def baseEnd_4396730 : Nat := 2257635798042688007354813

theorem tailTrace_4396730 : CollatzResearch.WordTrace tailWord_4396730 prefixEnd_4396730 2257635798042688007354813 := by
  unfold tailWord_4396730
  simp only [CollatzResearch.WordTrace]
  refine ⟨40090479340351396636692911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106907944907603724364514429 40090479340351396636692911)
  ·
    refine ⟨60135719010527094955039367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40090479340351396636692911 60135719010527094955039367)
    ·
      refine ⟨90203578515790642432559051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60135719010527094955039367 90203578515790642432559051)
      ·
        refine ⟨135305367773685963648838577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90203578515790642432559051 135305367773685963648838577)
        ·
          refine ⟨101479025830264472736628933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135305367773685963648838577 101479025830264472736628933)
          ·
            refine ⟨19027317343174588638117925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101479025830264472736628933 19027317343174588638117925)
            ·
              refine ⟨3567622001845235369647111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19027317343174588638117925 3567622001845235369647111)
              ·
                refine ⟨5351433002767853054470667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567622001845235369647111 5351433002767853054470667)
                ·
                  refine ⟨8027149504151779581706001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5351433002767853054470667 8027149504151779581706001)
                  ·
                    refine ⟨6020362128113834686279501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8027149504151779581706001 6020362128113834686279501)
                    ·
                      refine ⟨2257635798042688007354813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6020362128113834686279501 2257635798042688007354813)
                      ·
                        rfl

theorem cell23_4396730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_4396730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396730 prefixEnd_4396730 := by exact prefixLift 4396730
  have htrace : WordTrace (prefixWord ++ tailWord_4396730) baseStart_4396730 baseEnd_4396730 := by
    simpa [prefixWord, tailWord_4396730, baseEnd_4396730] using wordTrace_append hprefix tailTrace_4396730
  have hstable : (prefixWord ++ tailWord_4396730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396730).length < 2 ^ (prefixWord ++ tailWord_4396730).sum := by decide
  have hdescent : baseEnd_4396730 < baseStart_4396730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396743 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_4396743 : Nat := 118140960795 + 4396743 * 2 ^ 59
def prefixEnd_4396743 : Nat := 4983230072969 + 3 ^ 40 * 4396743 * 2
def baseEnd_4396743 : Nat := 2257642473291196456492253

theorem tailTrace_4396743 : CollatzResearch.WordTrace tailWord_4396743 prefixEnd_4396743 2257642473291196456492253 := by
  unfold tailWord_4396743
  simp only [CollatzResearch.WordTrace]
  refine ⟨160362391510358489766994883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106908261006905659844663255 160362391510358489766994883)
  ·
    refine ⟨240543587265537734650492325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160362391510358489766994883 240543587265537734650492325)
    ·
      refine ⟨45101922612288325246967311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240543587265537734650492325 45101922612288325246967311)
      ·
        refine ⟨67652883918432487870450967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45101922612288325246967311 67652883918432487870450967)
        ·
          refine ⟨101479325877648731805676451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67652883918432487870450967 101479325877648731805676451)
          ·
            refine ⟨152218988816473097708514677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101479325877648731805676451 152218988816473097708514677)
            ·
              refine ⟨14270530201544352910173251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152218988816473097708514677 14270530201544352910173251)
              ·
                refine ⟨21405795302316529365259877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14270530201544352910173251 21405795302316529365259877)
                ·
                  refine ⟨4013586619184349255986227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21405795302316529365259877 4013586619184349255986227)
                  ·
                    refine ⟨6020379928776523883979341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4013586619184349255986227 6020379928776523883979341)
                    ·
                      refine ⟨2257642473291196456492253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6020379928776523883979341 2257642473291196456492253)
                      ·
                        rfl

theorem cell23_4396743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_4396743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396743 prefixEnd_4396743 := by exact prefixLift 4396743
  have htrace : WordTrace (prefixWord ++ tailWord_4396743) baseStart_4396743 baseEnd_4396743 := by
    simpa [prefixWord, tailWord_4396743, baseEnd_4396743] using wordTrace_append hprefix tailTrace_4396743
  have hstable : (prefixWord ++ tailWord_4396743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396743).length < 2 ^ (prefixWord ++ tailWord_4396743).sum := by decide
  have hdescent : baseEnd_4396743 < baseStart_4396743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396783 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 3, 4, 2]
def baseStart_4396783 : Nat := 118140960795 + 4396783 * 2 ^ 59
def prefixEnd_4396783 : Nat := 4983230072969 + 3 ^ 40 * 4396783 * 2
def baseEnd_4396783 : Nat := 2257663012517376299992069

theorem tailTrace_4396783 : CollatzResearch.WordTrace tailWord_4396783 prefixEnd_4396783 2257663012517376299992069 := by
  unfold tailWord_4396783
  simp only [CollatzResearch.WordTrace]
  refine ⟨160363850430213576598451003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106909233620142384398967335 160363850430213576598451003)
  ·
    refine ⟨240545775645320364897676505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160363850430213576598451003 240545775645320364897676505)
    ·
      refine ⟨180409331733990273673257379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240545775645320364897676505 180409331733990273673257379)
      ·
        refine ⟨270613997600985410509886069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180409331733990273673257379 270613997600985410509886069)
        ·
          refine ⟨25370062275092382235301819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 270613997600985410509886069 25370062275092382235301819)
          ·
            refine ⟨38055093412638573352952729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25370062275092382235301819 38055093412638573352952729)
            ·
              refine ⟨28541320059478930014714547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38055093412638573352952729 28541320059478930014714547)
              ·
                refine ⟨42811980089218395022071821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28541320059478930014714547 42811980089218395022071821)
                ·
                  refine ⟨16054492533456898133276933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42811980089218395022071821 16054492533456898133276933)
                  ·
                    refine ⟨3010217350023168399989425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16054492533456898133276933 3010217350023168399989425)
                    ·
                      refine ⟨2257663012517376299992069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010217350023168399989425 2257663012517376299992069)
                      ·
                        rfl

theorem cell23_4396783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4, 2].length) (baseStart_4396783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396783 prefixEnd_4396783 := by exact prefixLift 4396783
  have htrace : WordTrace (prefixWord ++ tailWord_4396783) baseStart_4396783 baseEnd_4396783 := by
    simpa [prefixWord, tailWord_4396783, baseEnd_4396783] using wordTrace_append hprefix tailTrace_4396783
  have hstable : (prefixWord ++ tailWord_4396783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396783).length < 2 ^ (prefixWord ++ tailWord_4396783).sum := by decide
  have hdescent : baseEnd_4396783 < baseStart_4396783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396857 : List Nat := [1, 2, 1, 7, 1, 1, 1, 4, 5]
def baseStart_4396857 : Nat := 118140960795 + 4396857 * 2 ^ 59
def prefixEnd_4396857 : Nat := 4983230072969 + 3 ^ 40 * 4396857 * 2
def baseEnd_4396857 : Nat := 250855667787312112274081

theorem tailTrace_4396857 : CollatzResearch.WordTrace tailWord_4396857 prefixEnd_4396857 250855667787312112274081 := by
  unfold tailWord_4396857
  simp only [CollatzResearch.WordTrace]
  refine ⟨160366549431945487236644825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106911032954630324824429883 160366549431945487236644825)
  ·
    refine ⟨120274912073959115427483619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160366549431945487236644825 120274912073959115427483619)
    ·
      refine ⟨180412368110938673141225429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120274912073959115427483619 180412368110938673141225429)
      ·
        refine ⟨4228414877600125151747471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 180412368110938673141225429 4228414877600125151747471)
        ·
          refine ⟨6342622316400187727621207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228414877600125151747471 6342622316400187727621207)
          ·
            refine ⟨9513933474600281591431811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6342622316400187727621207 9513933474600281591431811)
            ·
              refine ⟨14270900211900422387147717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9513933474600281591431811 14270900211900422387147717)
              ·
                refine ⟨2675793789731329197590197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14270900211900422387147717 2675793789731329197590197)
                ·
                  refine ⟨250855667787312112274081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2675793789731329197590197 250855667787312112274081)
                  ·
                    rfl

theorem cell23_4396857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 5].length) (baseStart_4396857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396857 prefixEnd_4396857 := by exact prefixLift 4396857
  have htrace : WordTrace (prefixWord ++ tailWord_4396857) baseStart_4396857 baseEnd_4396857 := by
    simpa [prefixWord, tailWord_4396857, baseEnd_4396857] using wordTrace_append hprefix tailTrace_4396857
  have hstable : (prefixWord ++ tailWord_4396857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396857).length < 2 ^ (prefixWord ++ tailWord_4396857).sum := by decide
  have hdescent : baseEnd_4396857 < baseStart_4396857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396887 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 2, 5]
def baseStart_4396887 : Nat := 118140960795 + 4396887 * 2 ^ 59
def prefixEnd_4396887 : Nat := 4983230072969 + 3 ^ 40 * 4396887 * 2
def baseEnd_4396887 : Nat := 752572138168481297697197

theorem tailTrace_4396887 : CollatzResearch.WordTrace tailWord_4396887 prefixEnd_4396887 752572138168481297697197 := by
  unfold tailWord_4396887
  simp only [CollatzResearch.WordTrace]
  refine ⟨160367643621836802360236915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106911762414557868240157943 160367643621836802360236915)
  ·
    refine ⟨240551465432755203540355373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160367643621836802360236915 240551465432755203540355373)
    ·
      refine ⟨90206799537283201327633265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240551465432755203540355373 90206799537283201327633265)
      ·
        refine ⟨67655099652962400995724949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90206799537283201327633265 67655099652962400995724949)
        ·
          refine ⟨3171332796232612546674607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67655099652962400995724949 3171332796232612546674607)
          ·
            refine ⟨4756999194348918820011911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171332796232612546674607 4756999194348918820011911)
            ·
              refine ⟨7135498791523378230017867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756999194348918820011911 7135498791523378230017867)
              ·
                refine ⟨10703248187285067345026801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7135498791523378230017867 10703248187285067345026801)
                ·
                  refine ⟨8027436140463800508770101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10703248187285067345026801 8027436140463800508770101)
                  ·
                    refine ⟨752572138168481297697197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8027436140463800508770101 752572138168481297697197)
                    ·
                      rfl

theorem cell23_4396887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_4396887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396887 prefixEnd_4396887 := by exact prefixLift 4396887
  have htrace : WordTrace (prefixWord ++ tailWord_4396887) baseStart_4396887 baseEnd_4396887 := by
    simpa [prefixWord, tailWord_4396887, baseEnd_4396887] using wordTrace_append hprefix tailTrace_4396887
  have hstable : (prefixWord ++ tailWord_4396887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396887).length < 2 ^ (prefixWord ++ tailWord_4396887).sum := by decide
  have hdescent : baseEnd_4396887 < baseStart_4396887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396917 : List Nat := [1, 3, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4396917 : Nat := 118140960795 + 4396917 * 2 ^ 59
def prefixEnd_4396917 : Nat := 4983230072969 + 3 ^ 40 * 4396917 * 2
def baseEnd_4396917 : Nat := 752577272975026258572151

theorem tailTrace_4396917 : CollatzResearch.WordTrace tailWord_4396917 prefixEnd_4396917 752577272975026258572151 := by
  unfold tailWord_4396917
  simp only [CollatzResearch.WordTrace]
  refine ⟨160368737811728117483829005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106912491874485411655886003 160368737811728117483829005)
  ·
    refine ⟨60138276679398044056435877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160368737811728117483829005 60138276679398044056435877)
    ·
      refine ⟨11275926877387133260581727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60138276679398044056435877 11275926877387133260581727)
      ·
        refine ⟨16913890316080699890872591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11275926877387133260581727 16913890316080699890872591)
        ·
          refine ⟨25370835474121049836308887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16913890316080699890872591 25370835474121049836308887)
          ·
            refine ⟨38056253211181574754463331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25370835474121049836308887 38056253211181574754463331)
            ·
              refine ⟨57084379816772362131694997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38056253211181574754463331 57084379816772362131694997)
              ·
                refine ⟨2675830303911204474923203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57084379816772362131694997 2675830303911204474923203)
                ·
                  refine ⟨4013745455866806712384805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675830303911204474923203 4013745455866806712384805)
                  ·
                    refine ⟨752577272975026258572151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4013745455866806712384805 752577272975026258572151)
                    ·
                      rfl

theorem cell23_4396917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4396917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396917 prefixEnd_4396917 := by exact prefixLift 4396917
  have htrace : WordTrace (prefixWord ++ tailWord_4396917) baseStart_4396917 baseEnd_4396917 := by
    simpa [prefixWord, tailWord_4396917, baseEnd_4396917] using wordTrace_append hprefix tailTrace_4396917
  have hstable : (prefixWord ++ tailWord_4396917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396917).length < 2 ^ (prefixWord ++ tailWord_4396917).sum := by decide
  have hdescent : baseEnd_4396917 < baseStart_4396917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396963 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 4]
def baseStart_4396963 : Nat := 118140960795 + 4396963 * 2 ^ 59
def prefixEnd_4396963 : Nat := 4983230072969 + 3 ^ 40 * 4396963 * 2
def baseEnd_4396963 : Nat := 2257755439035185595741241

theorem tailTrace_4396963 : CollatzResearch.WordTrace tailWord_4396963 prefixEnd_4396963 2257755439035185595741241 := by
  unfold tailWord_4396963
  simp only [CollatzResearch.WordTrace]
  refine ⟨160370415569561467340003543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106913610379707644893335695 160370415569561467340003543)
  ·
    refine ⟨240555623354342201010005315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160370415569561467340003543 240555623354342201010005315)
    ·
      refine ⟨360833435031513301515007973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240555623354342201010005315 360833435031513301515007973)
      ·
        refine ⟨67656269068408744034063995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360833435031513301515007973 67656269068408744034063995)
        ·
          refine ⟨101484403602613116051095993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67656269068408744034063995 101484403602613116051095993)
          ·
            refine ⟨76113302701959837038321995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101484403602613116051095993 76113302701959837038321995)
            ·
              refine ⟨114169954052939755557482993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76113302701959837038321995 114169954052939755557482993)
              ·
                refine ⟨85627465539704816668112245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114169954052939755557482993 85627465539704816668112245)
                ·
                  refine ⟨8027574894347326562635523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85627465539704816668112245 8027574894347326562635523)
                  ·
                    refine ⟨12041362341520989843953285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8027574894347326562635523 12041362341520989843953285)
                    ·
                      refine ⟨2257755439035185595741241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12041362341520989843953285 2257755439035185595741241)
                      ·
                        rfl

theorem cell23_4396963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_4396963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396963 prefixEnd_4396963 := by exact prefixLift 4396963
  have htrace : WordTrace (prefixWord ++ tailWord_4396963) baseStart_4396963 baseEnd_4396963 := by
    simpa [prefixWord, tailWord_4396963, baseEnd_4396963] using wordTrace_append hprefix tailTrace_4396963
  have hstable : (prefixWord ++ tailWord_4396963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396963).length < 2 ^ (prefixWord ++ tailWord_4396963).sum := by decide
  have hdescent : baseEnd_4396963 < baseStart_4396963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396967 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_4396967 : Nat := 118140960795 + 4396967 * 2 ^ 59
def prefixEnd_4396967 : Nat := 4983230072969 + 3 ^ 40 * 4396967 * 2
def baseEnd_4396967 : Nat := 2257757492957803580091223

theorem tailTrace_4396967 : CollatzResearch.WordTrace tailWord_4396967 prefixEnd_4396967 2257757492957803580091223 := by
  unfold tailWord_4396967
  simp only [CollatzResearch.WordTrace]
  refine ⟨160370561461546976023149155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106913707641031317348766103 160370561461546976023149155)
  ·
    refine ⟨240555842192320464034723733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160370561461546976023149155 240555842192320464034723733)
    ·
      refine ⟨11276055102765021751627675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 240555842192320464034723733 11276055102765021751627675)
      ·
        refine ⟨16914082654147532627441513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11276055102765021751627675 16914082654147532627441513)
        ·
          refine ⟨12685561990610649470581135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16914082654147532627441513 12685561990610649470581135)
          ·
            refine ⟨19028342985915974205871703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12685561990610649470581135 19028342985915974205871703)
            ·
              refine ⟨28542514478873961308807555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19028342985915974205871703 28542514478873961308807555)
              ·
                refine ⟨42813771718310941963211333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28542514478873961308807555 42813771718310941963211333)
                ·
                  refine ⟨8027582197183301618102125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42813771718310941963211333 8027582197183301618102125)
                  ·
                    refine ⟨3010343323943738106788297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8027582197183301618102125 3010343323943738106788297)
                    ·
                      refine ⟨2257757492957803580091223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010343323943738106788297 2257757492957803580091223)
                      ·
                        rfl

theorem cell23_4396967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_4396967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396967 prefixEnd_4396967 := by exact prefixLift 4396967
  have htrace : WordTrace (prefixWord ++ tailWord_4396967) baseStart_4396967 baseEnd_4396967 := by
    simpa [prefixWord, tailWord_4396967, baseEnd_4396967] using wordTrace_append hprefix tailTrace_4396967
  have hstable : (prefixWord ++ tailWord_4396967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396967).length < 2 ^ (prefixWord ++ tailWord_4396967).sum := by decide
  have hdescent : baseEnd_4396967 < baseStart_4396967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396968 : List Nat := [2, 1, 6, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4396968 : Nat := 118140960795 + 4396968 * 2 ^ 59
def prefixEnd_4396968 : Nat := 4983230072969 + 3 ^ 40 * 4396968 * 2
def baseEnd_4396968 : Nat := 752586002146152692059573

theorem tailTrace_4396968 : CollatzResearch.WordTrace tailWord_4396968 prefixEnd_4396968 752586002146152692059573 := by
  unfold tailWord_4396968
  simp only [CollatzResearch.WordTrace]
  refine ⟨80185298967271676596967779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106913731956362235462623705 80185298967271676596967779)
  ·
    refine ⟨120277948450907514895451669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80185298967271676596967779 120277948450907514895451669)
    ·
      refine ⟨5638028833636289760724297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120277948450907514895451669 5638028833636289760724297)
      ·
        refine ⟨4228521625227217320543223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5638028833636289760724297 4228521625227217320543223)
        ·
          refine ⟨6342782437840825980814835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228521625227217320543223 6342782437840825980814835)
          ·
            refine ⟨9514173656761238971222253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6342782437840825980814835 9514173656761238971222253)
            ·
              refine ⟨3567815121285464614208345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9514173656761238971222253 3567815121285464614208345)
              ·
                refine ⟨2675861340964098460656259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3567815121285464614208345 2675861340964098460656259)
                ·
                  refine ⟨4013792011446147690984389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675861340964098460656259 4013792011446147690984389)
                  ·
                    refine ⟨752586002146152692059573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4013792011446147690984389 752586002146152692059573)
                    ·
                      rfl

theorem cell23_4396968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4396968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396968 prefixEnd_4396968 := by exact prefixLift 4396968
  have htrace : WordTrace (prefixWord ++ tailWord_4396968) baseStart_4396968 baseEnd_4396968 := by
    simpa [prefixWord, tailWord_4396968, baseEnd_4396968] using wordTrace_append hprefix tailTrace_4396968
  have hstable : (prefixWord ++ tailWord_4396968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396968).length < 2 ^ (prefixWord ++ tailWord_4396968).sum := by decide
  have hdescent : baseEnd_4396968 < baseStart_4396968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4396983 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_4396983 : Nat := 118140960795 + 4396983 * 2 ^ 59
def prefixEnd_4396983 : Nat := 4983230072969 + 3 ^ 40 * 4396983 * 2
def baseEnd_4396983 : Nat := 2257765708648275517491149

theorem tailTrace_4396983 : CollatzResearch.WordTrace tailWord_4396983 prefixEnd_4396983 2257765708648275517491149 := by
  unfold tailWord_4396983
  simp only [CollatzResearch.WordTrace]
  refine ⟨160371145029489010755731603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106914096686326007170487735 160371145029489010755731603)
  ·
    refine ⟨240556717544233516133597405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160371145029489010755731603 240556717544233516133597405)
    ·
      refine ⟨90208769079087568550099027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240556717544233516133597405 90208769079087568550099027)
      ·
        refine ⟨135313153618631352825148541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90208769079087568550099027 135313153618631352825148541)
        ·
          refine ⟨50742432606986757309430703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135313153618631352825148541 50742432606986757309430703)
          ·
            refine ⟨76113648910480135964146055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50742432606986757309430703 76113648910480135964146055)
            ·
              refine ⟨114170473365720203946219083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76113648910480135964146055 114170473365720203946219083)
              ·
                refine ⟨171255710048580305919328625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114170473365720203946219083 171255710048580305919328625)
                ·
                  refine ⟨128441782536435229439496469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171255710048580305919328625 128441782536435229439496469)
                  ·
                    refine ⟨6020708556395401379976397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 128441782536435229439496469 6020708556395401379976397)
                    ·
                      refine ⟨2257765708648275517491149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6020708556395401379976397 2257765708648275517491149)
                      ·
                        rfl

theorem cell23_4396983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_4396983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4396983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4396983 prefixEnd_4396983 := by exact prefixLift 4396983
  have htrace : WordTrace (prefixWord ++ tailWord_4396983) baseStart_4396983 baseEnd_4396983 := by
    simpa [prefixWord, tailWord_4396983, baseEnd_4396983] using wordTrace_append hprefix tailTrace_4396983
  have hstable : (prefixWord ++ tailWord_4396983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4396983).length < 2 ^ (prefixWord ++ tailWord_4396983).sum := by decide
  have hdescent : baseEnd_4396983 < baseStart_4396983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4396983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397017 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 5]
def baseStart_4397017 : Nat := 118140960795 + 4397017 * 2 ^ 59
def prefixEnd_4397017 : Nat := 4983230072969 + 3 ^ 40 * 4397017 * 2
def baseEnd_4397017 : Nat := 2257783166990528384465993

theorem tailTrace_4397017 : CollatzResearch.WordTrace tailWord_4397017 prefixEnd_4397017 2257783166990528384465993 := by
  unfold tailWord_4397017
  simp only [CollatzResearch.WordTrace]
  refine ⟨160372385111365834562469305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106914923407577223041646203 160372385111365834562469305)
  ·
    refine ⟨120279288833524375921851979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160372385111365834562469305 120279288833524375921851979)
    ·
      refine ⟨180418933250286563882777969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120279288833524375921851979 180418933250286563882777969)
      ·
        refine ⟨135314199937714922912083477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180418933250286563882777969 135314199937714922912083477)
        ·
          refine ⟨6342853122080387011503913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135314199937714922912083477 6342853122080387011503913)
          ·
            refine ⟨4757139841560290258627935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6342853122080387011503913 4757139841560290258627935)
            ·
              refine ⟨7135709762340435387941903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757139841560290258627935 7135709762340435387941903)
              ·
                refine ⟨10703564643510653081912855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7135709762340435387941903 10703564643510653081912855)
                ·
                  refine ⟨16055346965265979622869283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10703564643510653081912855 16055346965265979622869283)
                  ·
                    refine ⟨24083020447898969434303925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16055346965265979622869283 24083020447898969434303925)
                    ·
                      refine ⟨2257783166990528384465993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24083020447898969434303925 2257783166990528384465993)
                      ·
                        rfl

theorem cell23_4397017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_4397017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397017 prefixEnd_4397017 := by exact prefixLift 4397017
  have htrace : WordTrace (prefixWord ++ tailWord_4397017) baseStart_4397017 baseEnd_4397017 := by
    simpa [prefixWord, tailWord_4397017, baseEnd_4397017] using wordTrace_append hprefix tailTrace_4397017
  have hstable : (prefixWord ++ tailWord_4397017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397017).length < 2 ^ (prefixWord ++ tailWord_4397017).sum := by decide
  have hdescent : baseEnd_4397017 < baseStart_4397017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397057 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_4397057 : Nat := 118140960795 + 4397057 * 2 ^ 59
def prefixEnd_4397057 : Nat := 4983230072969 + 3 ^ 40 * 4397057 * 2
def baseEnd_4397057 : Nat := 2257803706216708227965809

theorem tailTrace_4397057 : CollatzResearch.WordTrace tailWord_4397057 prefixEnd_4397057 2257803706216708227965809 := by
  unfold tailWord_4397057
  simp only [CollatzResearch.WordTrace]
  refine ⟨160373844031220921393925425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106915896020813947595950283 160373844031220921393925425)
  ·
    refine ⟨120280383023415691045444069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160373844031220921393925425 120280383023415691045444069)
    ·
      refine ⟨22552571816890442071020763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120280383023415691045444069 22552571816890442071020763)
      ·
        refine ⟨33828857725335663106531145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22552571816890442071020763 33828857725335663106531145)
        ·
          refine ⟨25371643294001747329898359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33828857725335663106531145 25371643294001747329898359)
          ·
            refine ⟨38057464941002620994847539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25371643294001747329898359 38057464941002620994847539)
            ·
              refine ⟨57086197411503931492271309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38057464941002620994847539 57086197411503931492271309)
              ·
                refine ⟨21407324029313974309601741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57086197411503931492271309 21407324029313974309601741)
                ·
                  refine ⟨8027746510992740366100653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21407324029313974309601741 8027746510992740366100653)
                  ·
                    refine ⟨3010404941622277637287745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8027746510992740366100653 3010404941622277637287745)
                    ·
                      refine ⟨2257803706216708227965809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010404941622277637287745 2257803706216708227965809)
                      ·
                        rfl

theorem cell23_4397057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_4397057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397057 prefixEnd_4397057 := by exact prefixLift 4397057
  have htrace : WordTrace (prefixWord ++ tailWord_4397057) baseStart_4397057 baseEnd_4397057 := by
    simpa [prefixWord, tailWord_4397057, baseEnd_4397057] using wordTrace_append hprefix tailTrace_4397057
  have hstable : (prefixWord ++ tailWord_4397057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397057).length < 2 ^ (prefixWord ++ tailWord_4397057).sum := by decide
  have hdescent : baseEnd_4397057 < baseStart_4397057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397062 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4397062 : Nat := 118140960795 + 4397062 * 2 ^ 59
def prefixEnd_4397062 : Nat := 4983230072969 + 3 ^ 40 * 4397062 * 2
def baseEnd_4397062 : Nat := 752602091206660236134429

theorem tailTrace_4397062 : CollatzResearch.WordTrace tailWord_4397062 prefixEnd_4397062 752602091206660236134429 := by
  unfold tailWord_4397062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011688324881337726495545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106916017597468538165238293 5011688324881337726495545)
  ·
    refine ⟨3758766243661003294871659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5011688324881337726495545 3758766243661003294871659)
    ·
      refine ⟨5638149365491504942307489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758766243661003294871659 5638149365491504942307489)
      ·
        refine ⟨4228612024118628706730617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5638149365491504942307489 4228612024118628706730617)
        ·
          refine ⟨3171459018088971530047963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4228612024118628706730617 3171459018088971530047963)
          ·
            refine ⟨4757188527133457295071945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171459018088971530047963 4757188527133457295071945)
            ·
              refine ⟨3567891395350092971303959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4757188527133457295071945 3567891395350092971303959)
              ·
                refine ⟨5351837093025139456955939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567891395350092971303959 5351837093025139456955939)
                ·
                  refine ⟨8027755639537709185433909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5351837093025139456955939 8027755639537709185433909)
                  ·
                    refine ⟨752602091206660236134429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8027755639537709185433909 752602091206660236134429)
                    ·
                      rfl

theorem cell23_4397062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4397062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397062 prefixEnd_4397062 := by exact prefixLift 4397062
  have htrace : WordTrace (prefixWord ++ tailWord_4397062) baseStart_4397062 baseEnd_4397062 := by
    simpa [prefixWord, tailWord_4397062, baseEnd_4397062] using wordTrace_append hprefix tailTrace_4397062
  have hstable : (prefixWord ++ tailWord_4397062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397062).length < 2 ^ (prefixWord ++ tailWord_4397062).sum := by decide
  have hdescent : baseEnd_4397062 < baseStart_4397062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397104 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 1, 4, 2]
def baseStart_4397104 : Nat := 118140960795 + 4397104 * 2 ^ 59
def prefixEnd_4397104 : Nat := 4983230072969 + 3 ^ 40 * 4397104 * 2
def baseEnd_4397104 : Nat := 2257827839807469544078093

theorem tailTrace_4397104 : CollatzResearch.WordTrace tailWord_4397104 prefixEnd_4397104 2257827839807469544078093 := by
  unfold tailWord_4397104
  simp only [CollatzResearch.WordTrace]
  refine ⟨80187779131025324210443183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106917038841367098947257577 80187779131025324210443183)
  ·
    refine ⟨120281668696537986315664775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80187779131025324210443183 120281668696537986315664775)
    ·
      refine ⟨180422503044806979473497163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120281668696537986315664775 180422503044806979473497163)
      ·
        refine ⟨270633754567210469210245745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180422503044806979473497163 270633754567210469210245745)
        ·
          refine ⟨202975315925407851907684309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270633754567210469210245745 202975315925407851907684309)
          ·
            refine ⟨4757233967001746529086351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202975315925407851907684309 4757233967001746529086351)
            ·
              refine ⟨7135850950502619793629527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757233967001746529086351 7135850950502619793629527)
              ·
                refine ⟨10703776425753929690444291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7135850950502619793629527 10703776425753929690444291)
                ·
                  refine ⟨16055664638630894535666437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10703776425753929690444291 16055664638630894535666437)
                  ·
                    refine ⟨3010437119743292725437457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16055664638630894535666437 3010437119743292725437457)
                    ·
                      refine ⟨2257827839807469544078093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010437119743292725437457 2257827839807469544078093)
                      ·
                        rfl

theorem cell23_4397104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 4, 2].length) (baseStart_4397104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397104 prefixEnd_4397104 := by exact prefixLift 4397104
  have htrace : WordTrace (prefixWord ++ tailWord_4397104) baseStart_4397104 baseEnd_4397104 := by
    simpa [prefixWord, tailWord_4397104, baseEnd_4397104] using wordTrace_append hprefix tailTrace_4397104
  have hstable : (prefixWord ++ tailWord_4397104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397104).length < 2 ^ (prefixWord ++ tailWord_4397104).sum := by decide
  have hdescent : baseEnd_4397104 < baseStart_4397104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397108 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_4397108 : Nat := 118140960795 + 4397108 * 2 ^ 59
def prefixEnd_4397108 : Nat := 4983230072969 + 3 ^ 40 * 4397108 * 2
def baseEnd_4397108 : Nat := 2257829893730087528428075

theorem tailTrace_4397108 : CollatzResearch.WordTrace tailWord_4397108 prefixEnd_4397108 2257829893730087528428075 := by
  unfold tailWord_4397108
  simp only [CollatzResearch.WordTrace]
  refine ⟨80187852077018078552015989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106917136102690771402687985 80187852077018078552015989)
  ·
    refine ⟨7517611132220444864251499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80187852077018078552015989 7517611132220444864251499)
    ·
      refine ⟨11276416698330667296377249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517611132220444864251499 11276416698330667296377249)
      ·
        refine ⟨8457312523748000472282937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11276416698330667296377249 8457312523748000472282937)
        ·
          refine ⟨6342984392811000354212203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8457312523748000472282937 6342984392811000354212203)
          ·
            refine ⟨9514476589216500531318305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6342984392811000354212203 9514476589216500531318305)
            ·
              refine ⟨7135857441912375398488729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9514476589216500531318305 7135857441912375398488729)
              ·
                refine ⟨5351893081434281548866547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7135857441912375398488729 5351893081434281548866547)
                ·
                  refine ⟨8027839622151422323299821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5351893081434281548866547 8027839622151422323299821)
                  ·
                    refine ⟨3010439858306783371237433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8027839622151422323299821 3010439858306783371237433)
                    ·
                      refine ⟨2257829893730087528428075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010439858306783371237433 2257829893730087528428075)
                      ·
                        rfl

theorem cell23_4397108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_4397108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397108 prefixEnd_4397108 := by exact prefixLift 4397108
  have htrace : WordTrace (prefixWord ++ tailWord_4397108) baseStart_4397108 baseEnd_4397108 := by
    simpa [prefixWord, tailWord_4397108, baseEnd_4397108] using wordTrace_append hprefix tailTrace_4397108
  have hstable : (prefixWord ++ tailWord_4397108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397108).length < 2 ^ (prefixWord ++ tailWord_4397108).sum := by decide
  have hdescent : baseEnd_4397108 < baseStart_4397108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397144 : List Nat := [2, 1, 2, 2, 1, 5, 3, 2, 5]
def baseStart_4397144 : Nat := 118140960795 + 4397144 * 2 ^ 59
def prefixEnd_4397144 : Nat := 4983230072969 + 3 ^ 40 * 4397144 * 2
def baseEnd_4397144 : Nat := 250872042114849931953101

theorem tailTrace_4397144 : CollatzResearch.WordTrace tailWord_4397144 prefixEnd_4397144 250872042114849931953101 := by
  unfold tailWord_4397144
  simp only [CollatzResearch.WordTrace]
  refine ⟨80188508590952867626171243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106918011454603823501561657 80188508590952867626171243)
  ·
    refine ⟨120282762886429301439256865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80188508590952867626171243 120282762886429301439256865)
    ·
      refine ⟨90212072164821976079442649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120282762886429301439256865 90212072164821976079442649)
      ·
        refine ⟨67659054123616482059581987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90212072164821976079442649 67659054123616482059581987)
        ·
          refine ⟨101488581185424723089372981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67659054123616482059581987 101488581185424723089372981)
          ·
            refine ⟨9514554486133567789628717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101488581185424723089372981 9514554486133567789628717)
            ·
              refine ⟨3567957932300087921110769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9514554486133567789628717 3567957932300087921110769)
              ·
                refine ⟨2675968449225065940833077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3567957932300087921110769 2675968449225065940833077)
                ·
                  refine ⟨250872042114849931953101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2675968449225065940833077 250872042114849931953101)
                  ·
                    rfl

theorem cell23_4397144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 5].length) (baseStart_4397144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397144 prefixEnd_4397144 := by exact prefixLift 4397144
  have htrace : WordTrace (prefixWord ++ tailWord_4397144) baseStart_4397144 baseEnd_4397144 := by
    simpa [prefixWord, tailWord_4397144, baseEnd_4397144] using wordTrace_append hprefix tailTrace_4397144
  have hstable : (prefixWord ++ tailWord_4397144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397144).length < 2 ^ (prefixWord ++ tailWord_4397144).sum := by decide
  have hdescent : baseEnd_4397144 < baseStart_4397144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397174 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_4397174 : Nat := 118140960795 + 4397174 * 2 ^ 59
def prefixEnd_4397174 : Nat := 4983230072969 + 3 ^ 40 * 4397174 * 2
def baseEnd_4397174 : Nat := 752621261151094756734257

theorem tailTrace_4397174 : CollatzResearch.WordTrace tailWord_4397174 prefixEnd_4397174 752621261151094756734257 := by
  unfold tailWord_4397174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10023631960737315648495911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106918740914531366917289717 10023631960737315648495911)
  ·
    refine ⟨15035447941105973472743867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10023631960737315648495911 15035447941105973472743867)
    ·
      refine ⟨22553171911658960209115801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15035447941105973472743867 22553171911658960209115801)
      ·
        refine ⟨16914878933744220156836851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22553171911658960209115801 16914878933744220156836851)
        ·
          refine ⟨25372318400616330235255277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16914878933744220156836851 25372318400616330235255277)
          ·
            refine ⟨9514619400231123838220729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25372318400616330235255277 9514619400231123838220729)
            ·
              refine ⟨7135964550173342878665547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9514619400231123838220729 7135964550173342878665547)
              ·
                refine ⟨10703946825260014317998321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7135964550173342878665547 10703946825260014317998321)
                ·
                  refine ⟨8027960118945010738498741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10703946825260014317998321 8027960118945010738498741)
                  ·
                    refine ⟨752621261151094756734257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8027960118945010738498741 752621261151094756734257)
                    ·
                      rfl

theorem cell23_4397174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_4397174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397174 prefixEnd_4397174 := by exact prefixLift 4397174
  have htrace : WordTrace (prefixWord ++ tailWord_4397174) baseStart_4397174 baseEnd_4397174 := by
    simpa [prefixWord, tailWord_4397174, baseEnd_4397174] using wordTrace_append hprefix tailTrace_4397174
  have hstable : (prefixWord ++ tailWord_4397174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397174).length < 2 ^ (prefixWord ++ tailWord_4397174).sum := by decide
  have hdescent : baseEnd_4397174 < baseStart_4397174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397177 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_4397177 : Nat := 118140960795 + 4397177 * 2 ^ 59
def prefixEnd_4397177 : Nat := 4983230072969 + 3 ^ 40 * 4397177 * 2
def baseEnd_4397177 : Nat := 2257865323895247758465257

theorem tailTrace_4397177 : CollatzResearch.WordTrace tailWord_4397177 prefixEnd_4397177 2257865323895247758465257 := by
  unfold tailWord_4397177
  simp only [CollatzResearch.WordTrace]
  refine ⟨160378220790786181888293785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106918813860524121258862523 160378220790786181888293785)
  ·
    refine ⟨120283665593089636416220339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160378220790786181888293785 120283665593089636416220339)
    ·
      refine ⟨180425498389634454624330509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120283665593089636416220339 180425498389634454624330509)
      ·
        refine ⟨67659561896112920484123941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180425498389634454624330509 67659561896112920484123941)
        ·
          refine ⟨12686167855521172590773239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67659561896112920484123941 12686167855521172590773239)
          ·
            refine ⟨19029251783281758886159859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12686167855521172590773239 19029251783281758886159859)
            ·
              refine ⟨28543877674922638329239789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19029251783281758886159859 28543877674922638329239789)
              ·
                refine ⟨10703954128095989373464921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28543877674922638329239789 10703954128095989373464921)
                ·
                  refine ⟨8027965596071992030098691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10703954128095989373464921 8027965596071992030098691)
                  ·
                    refine ⟨12041948394107988045148037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8027965596071992030098691 12041948394107988045148037)
                    ·
                      refine ⟨2257865323895247758465257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12041948394107988045148037 2257865323895247758465257)
                      ·
                        rfl

theorem cell23_4397177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_4397177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397177 prefixEnd_4397177 := by exact prefixLift 4397177
  have htrace : WordTrace (prefixWord ++ tailWord_4397177) baseStart_4397177 baseEnd_4397177 := by
    simpa [prefixWord, tailWord_4397177, baseEnd_4397177] using wordTrace_append hprefix tailTrace_4397177
  have hstable : (prefixWord ++ tailWord_4397177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397177).length < 2 ^ (prefixWord ++ tailWord_4397177).sum := by decide
  have hdescent : baseEnd_4397177 < baseStart_4397177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397217 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 6]
def baseStart_4397217 : Nat := 118140960795 + 4397217 * 2 ^ 59
def prefixEnd_4397217 : Nat := 4983230072969 + 3 ^ 40 * 4397217 * 2
def baseEnd_4397217 : Nat := 250876207013491955773897

theorem tailTrace_4397217 : CollatzResearch.WordTrace tailWord_4397217 prefixEnd_4397217 250876207013491955773897 := by
  unfold tailWord_4397217
  simp only [CollatzResearch.WordTrace]
  refine ⟨160379679710641268719749905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106919786473760845813166603 160379679710641268719749905)
  ·
    refine ⟨120284759782980951539812429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160379679710641268719749905 120284759782980951539812429)
    ·
      refine ⟨45106784918617856827429661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120284759782980951539812429 45106784918617856827429661)
      ·
        refine ⟨16915044344481696310286123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45106784918617856827429661 16915044344481696310286123)
        ·
          refine ⟨25372566516722544465429185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16915044344481696310286123 25372566516722544465429185)
          ·
            refine ⟨19029424887541908349071889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25372566516722544465429185 19029424887541908349071889)
            ·
              refine ⟨14272068665656431261803917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19029424887541908349071889 14272068665656431261803917)
              ·
                refine ⟨5352025749621161723176469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14272068665656431261803917 5352025749621161723176469)
                ·
                  refine ⟨250876207013491955773897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5352025749621161723176469 250876207013491955773897)
                  ·
                    rfl

theorem cell23_4397217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 6].length) (baseStart_4397217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397217 prefixEnd_4397217 := by exact prefixLift 4397217
  have htrace : WordTrace (prefixWord ++ tailWord_4397217) baseStart_4397217 baseEnd_4397217 := by
    simpa [prefixWord, tailWord_4397217, baseEnd_4397217] using wordTrace_append hprefix tailTrace_4397217
  have hstable : (prefixWord ++ tailWord_4397217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397217).length < 2 ^ (prefixWord ++ tailWord_4397217).sum := by decide
  have hdescent : baseEnd_4397217 < baseStart_4397217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397267 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 4, 6, 2]
def baseStart_4397267 : Nat := 118140960795 + 4397267 * 2 ^ 59
def prefixEnd_4397267 : Nat := 4983230072969 + 3 ^ 40 * 4397267 * 2
def baseEnd_4397267 : Nat := 2257911537154152406339843

theorem tailTrace_4397267 : CollatzResearch.WordTrace tailWord_4397267 prefixEnd_4397267 2257911537154152406339843 := by
  unfold tailWord_4397267
  simp only [CollatzResearch.WordTrace]
  refine ⟨160381503360460127259070055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106921002240306751506046703 160381503360460127259070055)
  ·
    refine ⟨240572255040690190888605083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160381503360460127259070055 240572255040690190888605083)
    ·
      refine ⟨360858382561035286332907625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240572255040690190888605083 360858382561035286332907625)
      ·
        refine ⟨270643786920776464749680719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360858382561035286332907625 270643786920776464749680719)
        ·
          refine ⟨405965680381164697124521079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270643786920776464749680719 405965680381164697124521079)
          ·
            refine ⟨608948520571747045686781619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405965680381164697124521079 608948520571747045686781619)
            ·
              refine ⟨913422780857620568530172429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608948520571747045686781619 913422780857620568530172429)
              ·
                refine ⟨342533542821607713198814661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 913422780857620568530172429 342533542821607713198814661)
                ·
                  refine ⟨64225039279051446224777749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342533542821607713198814661 64225039279051446224777749)
                  ·
                    refine ⟨3010548716205536541786457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64225039279051446224777749 3010548716205536541786457)
                    ·
                      refine ⟨2257911537154152406339843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010548716205536541786457 2257911537154152406339843)
                      ·
                        rfl

theorem cell23_4397267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6, 2].length) (baseStart_4397267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397267 prefixEnd_4397267 := by exact prefixLift 4397267
  have htrace : WordTrace (prefixWord ++ tailWord_4397267) baseStart_4397267 baseEnd_4397267 := by
    simpa [prefixWord, tailWord_4397267, baseEnd_4397267] using wordTrace_append hprefix tailTrace_4397267
  have hstable : (prefixWord ++ tailWord_4397267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397267).length < 2 ^ (prefixWord ++ tailWord_4397267).sum := by decide
  have hdescent : baseEnd_4397267 < baseStart_4397267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397297 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_4397297 : Nat := 118140960795 + 4397297 * 2 ^ 59
def prefixEnd_4397297 : Nat := 4983230072969 + 3 ^ 40 * 4397297 * 2
def baseEnd_4397297 : Nat := 2257926941573787288964705

theorem tailTrace_4397297 : CollatzResearch.WordTrace tailWord_4397297 prefixEnd_4397297 2257926941573787288964705 := by
  unfold tailWord_4397297
  simp only [CollatzResearch.WordTrace]
  refine ⟨160382597550351442382662145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106921731700234294921774763 160382597550351442382662145)
  ·
    refine ⟨120286948162763581786996609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160382597550351442382662145 120286948162763581786996609)
    ·
      refine ⟨90215211122072686340247457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120286948162763581786996609 90215211122072686340247457)
      ·
        refine ⟨67661408341554514755185593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90215211122072686340247457 67661408341554514755185593)
        ·
          refine ⟨50746056256165886066389195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67661408341554514755185593 50746056256165886066389195)
          ·
            refine ⟨76119084384248829099583793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50746056256165886066389195 76119084384248829099583793)
            ·
              refine ⟨57089313288186621824687845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76119084384248829099583793 57089313288186621824687845)
              ·
                refine ⟨10704246241534991592128971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57089313288186621824687845 10704246241534991592128971)
                ·
                  refine ⟨16056369362302487388193457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10704246241534991592128971 16056369362302487388193457)
                  ·
                    refine ⟨12042277021726865541145093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16056369362302487388193457 12042277021726865541145093)
                    ·
                      refine ⟨2257926941573787288964705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12042277021726865541145093 2257926941573787288964705)
                      ·
                        rfl

theorem cell23_4397297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_4397297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397297 prefixEnd_4397297 := by exact prefixLift 4397297
  have htrace : WordTrace (prefixWord ++ tailWord_4397297) baseStart_4397297 baseEnd_4397297 := by
    simpa [prefixWord, tailWord_4397297, baseEnd_4397297] using wordTrace_append hprefix tailTrace_4397297
  have hstable : (prefixWord ++ tailWord_4397297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397297).length < 2 ^ (prefixWord ++ tailWord_4397297).sum := by decide
  have hdescent : baseEnd_4397297 < baseStart_4397297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397314 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4397314 : Nat := 118140960795 + 4397314 * 2 ^ 59
def prefixEnd_4397314 : Nat := 4983230072969 + 3 ^ 40 * 4397314 * 2
def baseEnd_4397314 : Nat := 2257935670744913722452127

theorem tailTrace_4397314 : CollatzResearch.WordTrace tailWord_4397314 prefixEnd_4397314 2257935670744913722452127 := by
  unfold tailWord_4397314
  simp only [CollatzResearch.WordTrace]
  refine ⟨40095804397822463571507749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106922145060859902857353997 40095804397822463571507749)
  ·
    refine ⟨7517963324591711919657703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40095804397822463571507749 7517963324591711919657703)
    ·
      refine ⟨11276944986887567879486555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517963324591711919657703 11276944986887567879486555)
      ·
        refine ⟨16915417480331351819229833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11276944986887567879486555 16915417480331351819229833)
        ·
          refine ⟨12686563110248513864422375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16915417480331351819229833 12686563110248513864422375)
          ·
            refine ⟨19029844665372770796633563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12686563110248513864422375 19029844665372770796633563)
            ·
              refine ⟨28544766998059156194950345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19029844665372770796633563 28544766998059156194950345)
              ·
                refine ⟨21408575248544367146212759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28544766998059156194950345 21408575248544367146212759)
                ·
                  refine ⟨32112862872816550719319139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21408575248544367146212759 32112862872816550719319139)
                  ·
                    refine ⟨48169294309224826078978709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32112862872816550719319139 48169294309224826078978709)
                    ·
                      refine ⟨2257935670744913722452127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48169294309224826078978709 2257935670744913722452127)
                      ·
                        rfl

theorem cell23_4397314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4397314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397314 prefixEnd_4397314 := by exact prefixLift 4397314
  have htrace : WordTrace (prefixWord ++ tailWord_4397314) baseStart_4397314 baseEnd_4397314 := by
    simpa [prefixWord, tailWord_4397314, baseEnd_4397314] using wordTrace_append hprefix tailTrace_4397314
  have hstable : (prefixWord ++ tailWord_4397314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397314).length < 2 ^ (prefixWord ++ tailWord_4397314).sum := by decide
  have hdescent : baseEnd_4397314 < baseStart_4397314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397317 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_4397317 : Nat := 118140960795 + 4397317 * 2 ^ 59
def prefixEnd_4397317 : Nat := 4983230072969 + 3 ^ 40 * 4397317 * 2
def baseEnd_4397317 : Nat := 2257937211186877210714613

theorem tailTrace_4397317 : CollatzResearch.WordTrace tailWord_4397317 prefixEnd_4397317 2257937211186877210714613 := by
  unfold tailWord_4397317
  simp only [CollatzResearch.WordTrace]
  refine ⟨160383327010278985798390205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106922218006852657198926803 160383327010278985798390205)
  ·
    refine ⟨60143747628854619674396327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160383327010278985798390205 60143747628854619674396327)
    ·
      refine ⟨90215621443281929511594491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60143747628854619674396327 90215621443281929511594491)
      ·
        refine ⟨135323432164922894267391737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90215621443281929511594491 135323432164922894267391737)
        ·
          refine ⟨101492574123692170700543803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135323432164922894267391737 101492574123692170700543803)
          ·
            refine ⟨152238861185538256050815705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101492574123692170700543803 152238861185538256050815705)
            ·
              refine ⟨114179145889153692038111779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152238861185538256050815705 114179145889153692038111779)
              ·
                refine ⟨171268718833730538057167669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114179145889153692038111779 171268718833730538057167669)
                ·
                  refine ⟨16056442390662237942859469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171268718833730538057167669 16056442390662237942859469)
                  ·
                    refine ⟨6021165896498339228572301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16056442390662237942859469 6021165896498339228572301)
                    ·
                      refine ⟨2257937211186877210714613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021165896498339228572301 2257937211186877210714613)
                      ·
                        rfl

theorem cell23_4397317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_4397317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397317 prefixEnd_4397317 := by exact prefixLift 4397317
  have htrace : WordTrace (prefixWord ++ tailWord_4397317) baseStart_4397317 baseEnd_4397317 := by
    simpa [prefixWord, tailWord_4397317, baseEnd_4397317] using wordTrace_append hprefix tailTrace_4397317
  have hstable : (prefixWord ++ tailWord_4397317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397317).length < 2 ^ (prefixWord ++ tailWord_4397317).sum := by decide
  have hdescent : baseEnd_4397317 < baseStart_4397317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397338 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_4397338 : Nat := 118140960795 + 4397338 * 2 ^ 59
def prefixEnd_4397338 : Nat := 4983230072969 + 3 ^ 40 * 4397338 * 2
def baseEnd_4397338 : Nat := 2257947994280621628552017

theorem tailTrace_4397338 : CollatzResearch.WordTrace tailWord_4397338 prefixEnd_4397338 2257947994280621628552017 := by
  unfold tailWord_4397338
  simp only [CollatzResearch.WordTrace]
  refine ⟨40096023235800726596226167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106922728628801937589936445 40096023235800726596226167)
  ·
    refine ⟨60144034853701089894339251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40096023235800726596226167 60144034853701089894339251)
    ·
      refine ⟨90216052280551634841508877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60144034853701089894339251 90216052280551634841508877)
      ·
        refine ⟨33831019605206863065565829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90216052280551634841508877 33831019605206863065565829)
        ·
          refine ⟨6343316175976286824793593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33831019605206863065565829 6343316175976286824793593)
          ·
            refine ⟨4757487131982215118595195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343316175976286824793593 4757487131982215118595195)
            ·
              refine ⟨7136230697973322677892793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757487131982215118595195 7136230697973322677892793)
              ·
                refine ⟨5352173023479992008419595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7136230697973322677892793 5352173023479992008419595)
                ·
                  refine ⟨8028259535219988012629393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352173023479992008419595 8028259535219988012629393)
                  ·
                    refine ⟨6021194651414991009472045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8028259535219988012629393 6021194651414991009472045)
                    ·
                      refine ⟨2257947994280621628552017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021194651414991009472045 2257947994280621628552017)
                      ·
                        rfl

theorem cell23_4397338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_4397338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397338 prefixEnd_4397338 := by exact prefixLift 4397338
  have htrace : WordTrace (prefixWord ++ tailWord_4397338) baseStart_4397338 baseEnd_4397338 := by
    simpa [prefixWord, tailWord_4397338, baseEnd_4397338] using wordTrace_append hprefix tailTrace_4397338
  have hstable : (prefixWord ++ tailWord_4397338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397338).length < 2 ^ (prefixWord ++ tailWord_4397338).sum := by decide
  have hdescent : baseEnd_4397338 < baseStart_4397338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397374 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4397374 : Nat := 118140960795 + 4397374 * 2 ^ 59
def prefixEnd_4397374 : Nat := 4983230072969 + 3 ^ 40 * 4397374 * 2
def baseEnd_4397374 : Nat := 2257966479584183487701851

theorem tailTrace_4397374 : CollatzResearch.WordTrace tailWord_4397374 prefixEnd_4397374 2257966479584183487701851 := by
  unfold tailWord_4397374
  simp only [CollatzResearch.WordTrace]
  refine ⟨20048175746384060566651897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106923603980714989688810117 20048175746384060566651897)
  ·
    refine ⟨15036131809788045424988923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20048175746384060566651897 15036131809788045424988923)
    ·
      refine ⟨22554197714682068137483385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15036131809788045424988923 22554197714682068137483385)
      ·
        refine ⟨16915648286011551103112539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22554197714682068137483385 16915648286011551103112539)
        ·
          refine ⟨25373472429017326654668809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16915648286011551103112539 25373472429017326654668809)
          ·
            refine ⟨19030104321762994991001607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25373472429017326654668809 19030104321762994991001607)
            ·
              refine ⟨28545156482644492486502411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19030104321762994991001607 28545156482644492486502411)
              ·
                refine ⟨42817734723966738729753617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28545156482644492486502411 42817734723966738729753617)
                ·
                  refine ⟨32113301042975054047315213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42817734723966738729753617 32113301042975054047315213)
                  ·
                    refine ⟨12042487891115645267743205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32113301042975054047315213 12042487891115645267743205)
                    ·
                      refine ⟨2257966479584183487701851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12042487891115645267743205 2257966479584183487701851)
                      ·
                        rfl

theorem cell23_4397374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4397374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397374 prefixEnd_4397374 := by exact prefixLift 4397374
  have htrace : WordTrace (prefixWord ++ tailWord_4397374) baseStart_4397374 baseEnd_4397374 := by
    simpa [prefixWord, tailWord_4397374, baseEnd_4397374] using wordTrace_append hprefix tailTrace_4397374
  have hstable : (prefixWord ++ tailWord_4397374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397374).length < 2 ^ (prefixWord ++ tailWord_4397374).sum := by decide
  have hdescent : baseEnd_4397374 < baseStart_4397374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397406 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4397406 : Nat := 118140960795 + 4397406 * 2 ^ 59
def prefixEnd_4397406 : Nat := 4983230072969 + 3 ^ 40 * 4397406 * 2
def baseEnd_4397406 : Nat := 2257982910965127362501705

theorem tailTrace_4397406 : CollatzResearch.WordTrace tailWord_4397406 prefixEnd_4397406 2257982910965127362501705 := by
  unfold tailWord_4397406
  simp only [CollatzResearch.WordTrace]
  refine ⟨20048321638369569249797509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106924382071304369332253381 20048321638369569249797509)
  ·
    refine ⟨3759060307194294234337033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20048321638369569249797509 3759060307194294234337033)
    ·
      refine ⟨2819295230395720675752775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3759060307194294234337033 2819295230395720675752775)
      ·
        refine ⟨4228942845593581013629163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819295230395720675752775 4228942845593581013629163)
        ·
          refine ⟨6343414268390371520443745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228942845593581013629163 6343414268390371520443745)
          ·
            refine ⟨4757560701292778640332809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343414268390371520443745 4757560701292778640332809)
            ·
              refine ⟨3568170525969583980249607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4757560701292778640332809 3568170525969583980249607)
              ·
                refine ⟨5352255788954375970374411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3568170525969583980249607 5352255788954375970374411)
                ·
                  refine ⟨8028383683431563955561617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352255788954375970374411 8028383683431563955561617)
                  ·
                    refine ⟨6021287762573672966671213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8028383683431563955561617 6021287762573672966671213)
                    ·
                      refine ⟨2257982910965127362501705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021287762573672966671213 2257982910965127362501705)
                      ·
                        rfl

theorem cell23_4397406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4397406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397406 prefixEnd_4397406 := by exact prefixLift 4397406
  have htrace : WordTrace (prefixWord ++ tailWord_4397406) baseStart_4397406 baseEnd_4397406 := by
    simpa [prefixWord, tailWord_4397406, baseEnd_4397406] using wordTrace_append hprefix tailTrace_4397406
  have hstable : (prefixWord ++ tailWord_4397406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397406).length < 2 ^ (prefixWord ++ tailWord_4397406).sum := by decide
  have hdescent : baseEnd_4397406 < baseStart_4397406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397424 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3]
def baseStart_4397424 : Nat := 118140960795 + 4397424 * 2 ^ 59
def prefixEnd_4397424 : Nat := 4983230072969 + 3 ^ 40 * 4397424 * 2
def baseEnd_4397424 : Nat := 2257992153616908292076621

theorem tailTrace_4397424 : CollatzResearch.WordTrace tailWord_4397424 prefixEnd_4397424 2257992153616908292076621 := by
  unfold tailWord_4397424
  simp only [CollatzResearch.WordTrace]
  refine ⟨80193614810445671536267663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106924819747260895381690217 80193614810445671536267663)
  ·
    refine ⟨120290422215668507304401495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80193614810445671536267663 120290422215668507304401495)
    ·
      refine ⟨180435633323502760956602243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120290422215668507304401495 180435633323502760956602243)
      ·
        refine ⟨270653449985254141434903365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180435633323502760956602243 270653449985254141434903365)
        ·
          refine ⟨50747521872235151519044381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270653449985254141434903365 50747521872235151519044381)
          ·
            refine ⟨19030320702088181819641643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50747521872235151519044381 19030320702088181819641643)
            ·
              refine ⟨28545481053132272729462465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19030320702088181819641643 28545481053132272729462465)
              ·
                refine ⟨21409110789849204547096849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28545481053132272729462465 21409110789849204547096849)
                ·
                  refine ⟨16056833092386903410322637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21409110789849204547096849 16056833092386903410322637)
                  ·
                    refine ⟨6021312409645088778870989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16056833092386903410322637 6021312409645088778870989)
                    ·
                      refine ⟨2257992153616908292076621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021312409645088778870989 2257992153616908292076621)
                      ·
                        rfl

theorem cell23_4397424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_4397424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397424 prefixEnd_4397424 := by exact prefixLift 4397424
  have htrace : WordTrace (prefixWord ++ tailWord_4397424) baseStart_4397424 baseEnd_4397424 := by
    simpa [prefixWord, tailWord_4397424, baseEnd_4397424] using wordTrace_append hprefix tailTrace_4397424
  have hstable : (prefixWord ++ tailWord_4397424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397424).length < 2 ^ (prefixWord ++ tailWord_4397424).sum := by decide
  have hdescent : baseEnd_4397424 < baseStart_4397424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397441 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4397441 : Nat := 118140960795 + 4397441 * 2 ^ 59
def prefixEnd_4397441 : Nat := 4983230072969 + 3 ^ 40 * 4397441 * 2
def baseEnd_4397441 : Nat := 2258000882788034725564043

theorem tailTrace_4397441 : CollatzResearch.WordTrace tailWord_4397441 prefixEnd_4397441 2258000882788034725564043 := by
  unfold tailWord_4397441
  simp only [CollatzResearch.WordTrace]
  refine ⟨160387849661829754975904177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106925233107886503317269451 160387849661829754975904177)
  ·
    refine ⟨120290887246372316231928133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160387849661829754975904177 120290887246372316231928133)
    ·
      refine ⟨22554541358694809293486525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120290887246372316231928133 22554541358694809293486525)
      ·
        refine ⟨8457953009510553485057447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22554541358694809293486525 8457953009510553485057447)
        ·
          refine ⟨12686929514265830227586171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8457953009510553485057447 12686929514265830227586171)
          ·
            refine ⟨19030394271398745341379257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12686929514265830227586171 19030394271398745341379257)
            ·
              refine ⟨14272795703549059006034443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19030394271398745341379257 14272795703549059006034443)
              ·
                refine ⟨21409193555323588509051665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14272795703549059006034443 21409193555323588509051665)
                ·
                  refine ⟨16056895166492691381788749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21409193555323588509051665 16056895166492691381788749)
                  ·
                    refine ⟨6021335687434759268170781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16056895166492691381788749 6021335687434759268170781)
                    ·
                      refine ⟨2258000882788034725564043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021335687434759268170781 2258000882788034725564043)
                      ·
                        rfl

theorem cell23_4397441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4397441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397441 prefixEnd_4397441 := by exact prefixLift 4397441
  have htrace : WordTrace (prefixWord ++ tailWord_4397441) baseStart_4397441 baseEnd_4397441 := by
    simpa [prefixWord, tailWord_4397441, baseEnd_4397441] using wordTrace_append hprefix tailTrace_4397441
  have hstable : (prefixWord ++ tailWord_4397441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397441).length < 2 ^ (prefixWord ++ tailWord_4397441).sum := by decide
  have hdescent : baseEnd_4397441 < baseStart_4397441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397442 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_4397442 : Nat := 118140960795 + 4397442 * 2 ^ 59
def prefixEnd_4397442 : Nat := 4983230072969 + 3 ^ 40 * 4397442 * 2
def baseEnd_4397442 : Nat := 2258001396268689221651539

theorem tailTrace_4397442 : CollatzResearch.WordTrace tailWord_4397442 prefixEnd_4397442 2258001396268689221651539 := by
  unfold tailWord_4397442
  simp only [CollatzResearch.WordTrace]
  refine ⟨40096971533706533036672645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106925257423217421431127053 40096971533706533036672645)
  ·
    refine ⟨7518182162569974944376121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40096971533706533036672645 7518182162569974944376121)
    ·
      refine ⟨5638636621927481208282091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7518182162569974944376121 5638636621927481208282091)
      ·
        refine ⟨8457954932891221812423137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5638636621927481208282091 8457954932891221812423137)
        ·
          refine ⟨6343466199668416359317353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8457954932891221812423137 6343466199668416359317353)
          ·
            refine ⟨4757599649751312269488015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343466199668416359317353 4757599649751312269488015)
            ·
              refine ⟨7136399474626968404232023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757599649751312269488015 7136399474626968404232023)
              ·
                refine ⟨10704599211940452606348035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7136399474626968404232023 10704599211940452606348035)
                ·
                  refine ⟨16056898817910678909522053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10704599211940452606348035 16056898817910678909522053)
                  ·
                    refine ⟨3010668528358252295535385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16056898817910678909522053 3010668528358252295535385)
                    ·
                      refine ⟨2258001396268689221651539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010668528358252295535385 2258001396268689221651539)
                      ·
                        rfl

theorem cell23_4397442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_4397442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397442 prefixEnd_4397442 := by exact prefixLift 4397442
  have htrace : WordTrace (prefixWord ++ tailWord_4397442) baseStart_4397442 baseEnd_4397442 := by
    simpa [prefixWord, tailWord_4397442, baseEnd_4397442] using wordTrace_append hprefix tailTrace_4397442
  have hstable : (prefixWord ++ tailWord_4397442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397442).length < 2 ^ (prefixWord ++ tailWord_4397442).sum := by decide
  have hdescent : baseEnd_4397442 < baseStart_4397442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397482 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 7]
def baseStart_4397482 : Nat := 118140960795 + 4397482 * 2 ^ 59
def prefixEnd_4397482 : Nat := 4983230072969 + 3 ^ 40 * 4397482 * 2
def baseEnd_4397482 : Nat := 250891326166096562794595

theorem tailTrace_4397482 : CollatzResearch.WordTrace tailWord_4397482 prefixEnd_4397482 250891326166096562794595 := by
  unfold tailWord_4397482
  simp only [CollatzResearch.WordTrace]
  refine ⟨40097336263670304744536675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106926230036454145985431133 40097336263670304744536675)
  ·
    refine ⟨60146004395505457116805013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40097336263670304744536675 60146004395505457116805013)
    ·
      refine ⟨2819343956039318302350235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60146004395505457116805013 2819343956039318302350235)
      ·
        refine ⟨4229015934058977453525353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819343956039318302350235 4229015934058977453525353)
        ·
          refine ⟨3171761950544233090144015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4229015934058977453525353 3171761950544233090144015)
          ·
            refine ⟨4757642925816349635216023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171761950544233090144015 4757642925816349635216023)
            ·
              refine ⟨7136464388724524452824035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757642925816349635216023 7136464388724524452824035)
              ·
                refine ⟨10704696583086786679236053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7136464388724524452824035 10704696583086786679236053)
                ·
                  refine ⟨250891326166096562794595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10704696583086786679236053 250891326166096562794595)
                  ·
                    rfl

theorem cell23_4397482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_4397482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397482 prefixEnd_4397482 := by exact prefixLift 4397482
  have htrace : WordTrace (prefixWord ++ tailWord_4397482) baseStart_4397482 baseEnd_4397482 := by
    simpa [prefixWord, tailWord_4397482, baseEnd_4397482] using wordTrace_append hprefix tailTrace_4397482
  have hstable : (prefixWord ++ tailWord_4397482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397482).length < 2 ^ (prefixWord ++ tailWord_4397482).sum := by decide
  have hdescent : baseEnd_4397482 < baseStart_4397482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397558 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_4397558 : Nat := 118140960795 + 4397558 * 2 ^ 59
def prefixEnd_4397558 : Nat := 4983230072969 + 3 ^ 40 * 4397558 * 2
def baseEnd_4397558 : Nat := 2258060960024610767801005

theorem tailTrace_4397558 : CollatzResearch.WordTrace tailWord_4397558 prefixEnd_4397558 2258060960024610767801005 := by
  unfold tailWord_4397558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10024507312650367747369583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106928078001603922638608885 10024507312650367747369583)
  ·
    refine ⟨15036760968975551621054375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10024507312650367747369583 15036760968975551621054375)
    ·
      refine ⟨22555141453463327431581563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15036760968975551621054375 22555141453463327431581563)
      ·
        refine ⟨33832712180194991147372345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22555141453463327431581563 33832712180194991147372345)
        ·
          refine ⟨25374534135146243360529259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33832712180194991147372345 25374534135146243360529259)
          ·
            refine ⟨38061801202719365040793889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25374534135146243360529259 38061801202719365040793889)
            ·
              refine ⟨28546350902039523780595417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38061801202719365040793889 28546350902039523780595417)
              ·
                refine ⟨21409763176529642835446563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28546350902039523780595417 21409763176529642835446563)
                ·
                  refine ⟨32114644764794464253169845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21409763176529642835446563 32114644764794464253169845)
                  ·
                    refine ⟨3010747946699481023734673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32114644764794464253169845 3010747946699481023734673)
                    ·
                      refine ⟨2258060960024610767801005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010747946699481023734673 2258060960024610767801005)
                      ·
                        rfl

theorem cell23_4397558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_4397558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397558 prefixEnd_4397558 := by exact prefixLift 4397558
  have htrace : WordTrace (prefixWord ++ tailWord_4397558) baseStart_4397558 baseEnd_4397558 := by
    simpa [prefixWord, tailWord_4397558, baseEnd_4397558] using wordTrace_append hprefix tailTrace_4397558
  have hstable : (prefixWord ++ tailWord_4397558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397558).length < 2 ^ (prefixWord ++ tailWord_4397558).sum := by decide
  have hdescent : baseEnd_4397558 < baseStart_4397558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397571 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 4]
def baseStart_4397571 : Nat := 118140960795 + 4397571 * 2 ^ 59
def prefixEnd_4397571 : Nat := 4983230072969 + 3 ^ 40 * 4397571 * 2
def baseEnd_4397571 : Nat := 2258067635273119216938445

theorem tailTrace_4397571 : CollatzResearch.WordTrace tailWord_4397571 prefixEnd_4397571 2258067635273119216938445 := by
  unfold tailWord_4397571
  simp only [CollatzResearch.WordTrace]
  refine ⟨160392591151358787178136567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106928394100905858118757711 160392591151358787178136567)
  ·
    refine ⟨240588886727038180767204851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160392591151358787178136567 240588886727038180767204851)
    ·
      refine ⟨360883330090557271150807277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240588886727038180767204851 360883330090557271150807277)
      ·
        refine ⟨135331248783958976681552729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360883330090557271150807277 135331248783958976681552729)
        ·
          refine ⟨101498436587969232511164547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135331248783958976681552729 101498436587969232511164547)
          ·
            refine ⟨152247654881953848766746821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101498436587969232511164547 152247654881953848766746821)
            ·
              refine ⟨28546435290366346643765029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152247654881953848766746821 28546435290366346643765029)
              ·
                refine ⟨5352456616943689995705943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28546435290366346643765029 5352456616943689995705943)
                ·
                  refine ⟨8028684925415534993558915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352456616943689995705943 8028684925415534993558915)
                  ·
                    refine ⟨12043027388123302490338373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8028684925415534993558915 12043027388123302490338373)
                    ·
                      refine ⟨2258067635273119216938445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12043027388123302490338373 2258067635273119216938445)
                      ·
                        rfl

theorem cell23_4397571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_4397571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397571 prefixEnd_4397571 := by exact prefixLift 4397571
  have htrace : WordTrace (prefixWord ++ tailWord_4397571) baseStart_4397571 baseEnd_4397571 := by
    simpa [prefixWord, tailWord_4397571, baseEnd_4397571] using wordTrace_append hprefix tailTrace_4397571
  have hstable : (prefixWord ++ tailWord_4397571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397571).length < 2 ^ (prefixWord ++ tailWord_4397571).sum := by decide
  have hdescent : baseEnd_4397571 < baseStart_4397571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397582 : List Nat := [4, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4397582 : Nat := 118140960795 + 4397582 * 2 ^ 59
def prefixEnd_4397582 : Nat := 4983230072969 + 3 ^ 40 * 4397582 * 2
def baseEnd_4397582 : Nat := 2258073283560318673900895

theorem tailTrace_4397582 : CollatzResearch.WordTrace tailWord_4397582 prefixEnd_4397582 2258073283560318673900895 := by
  unfold tailWord_4397582
  simp only [CollatzResearch.WordTrace]
  refine ⟨20049124044289867007098375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106928661569545957371191333 20049124044289867007098375)
  ·
    refine ⟨30073686066434800510647563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20049124044289867007098375 30073686066434800510647563)
    ·
      refine ⟨45110529099652200765971345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30073686066434800510647563 45110529099652200765971345)
      ·
        refine ⟨33832896824739150574478509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45110529099652200765971345 33832896824739150574478509)
        ·
          refine ⟨12687336309277181465429441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33832896824739150574478509 12687336309277181465429441)
          ·
            refine ⟨9515502231957886099072081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12687336309277181465429441 9515502231957886099072081)
            ·
              refine ⟨7136626673968414574304061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9515502231957886099072081 7136626673968414574304061)
              ·
                refine ⟨2676235002738155465364023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7136626673968414574304061 2676235002738155465364023)
                ·
                  refine ⟨4014352504107233198046035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676235002738155465364023 4014352504107233198046035)
                  ·
                    refine ⟨6021528756160849797069053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4014352504107233198046035 6021528756160849797069053)
                    ·
                      refine ⟨2258073283560318673900895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021528756160849797069053 2258073283560318673900895)
                      ·
                        rfl

theorem cell23_4397582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4397582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397582 prefixEnd_4397582 := by exact prefixLift 4397582
  have htrace : WordTrace (prefixWord ++ tailWord_4397582) baseStart_4397582 baseEnd_4397582 := by
    simpa [prefixWord, tailWord_4397582, baseEnd_4397582] using wordTrace_append hprefix tailTrace_4397582
  have hstable : (prefixWord ++ tailWord_4397582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397582).length < 2 ^ (prefixWord ++ tailWord_4397582).sum := by decide
  have hdescent : baseEnd_4397582 < baseStart_4397582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397584 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_4397584 : Nat := 118140960795 + 4397584 * 2 ^ 59
def prefixEnd_4397584 : Nat := 4983230072969 + 3 ^ 40 * 4397584 * 2
def baseEnd_4397584 : Nat := 2258074310521627666075885

theorem tailTrace_4397584 : CollatzResearch.WordTrace tailWord_4397584 prefixEnd_4397584 2258074310521627666075885 := by
  unfold tailWord_4397584
  simp only [CollatzResearch.WordTrace]
  refine ⟨80196532650155845199179903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106928710200207793598906537 80196532650155845199179903)
  ·
    refine ⟨120294798975233767798769855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80196532650155845199179903 120294798975233767798769855)
    ·
      refine ⟨180442198462850651698154783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120294798975233767798769855 180442198462850651698154783)
      ·
        refine ⟨270663297694275977547232175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180442198462850651698154783 270663297694275977547232175)
        ·
          refine ⟨405994946541413966320848263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270663297694275977547232175 405994946541413966320848263)
          ·
            refine ⟨608992419812120949481272395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405994946541413966320848263 608992419812120949481272395)
            ·
              refine ⟨913488629718181424221908593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608992419812120949481272395 913488629718181424221908593)
              ·
                refine ⟨685116472288636068166431445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 913488629718181424221908593 685116472288636068166431445)
                ·
                  refine ⟨16057417319264907847650737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 685116472288636068166431445 16057417319264907847650737)
                  ·
                    refine ⟨12043062989448680885738053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16057417319264907847650737 12043062989448680885738053)
                    ·
                      refine ⟨2258074310521627666075885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12043062989448680885738053 2258074310521627666075885)
                      ·
                        rfl

theorem cell23_4397584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_4397584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397584 prefixEnd_4397584 := by exact prefixLift 4397584
  have htrace : WordTrace (prefixWord ++ tailWord_4397584) baseStart_4397584 baseEnd_4397584 := by
    simpa [prefixWord, tailWord_4397584, baseEnd_4397584] using wordTrace_append hprefix tailTrace_4397584
  have hstable : (prefixWord ++ tailWord_4397584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397584).length < 2 ^ (prefixWord ++ tailWord_4397584).sum := by decide
  have hdescent : baseEnd_4397584 < baseStart_4397584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397608 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4397608 : Nat := 118140960795 + 4397608 * 2 ^ 59
def prefixEnd_4397608 : Nat := 4983230072969 + 3 ^ 40 * 4397608 * 2
def baseEnd_4397608 : Nat := 2258086634057335572175775

theorem tailTrace_4397608 : CollatzResearch.WordTrace tailWord_4397608 prefixEnd_4397608 2258086634057335572175775 := by
  unfold tailWord_4397608
  simp only [CollatzResearch.WordTrace]
  refine ⟨80196970326112371248616739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106929293768149828331488985 80196970326112371248616739)
  ·
    refine ⟨120295455489168556872925109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80196970326112371248616739 120295455489168556872925109)
    ·
      refine ⟨11277698952109552206836729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120295455489168556872925109 11277698952109552206836729)
      ·
        refine ⟨8458274214082164155127547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11277698952109552206836729 8458274214082164155127547)
        ·
          refine ⟨12687411321123246232691321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8458274214082164155127547 12687411321123246232691321)
          ·
            refine ⟨9515558490842434674518491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12687411321123246232691321 9515558490842434674518491)
            ·
              refine ⟨14273337736263652011777737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9515558490842434674518491 14273337736263652011777737)
              ·
                refine ⟨10705003302197739008833303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14273337736263652011777737 10705003302197739008833303)
                ·
                  refine ⟨16057504953296608513249955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10705003302197739008833303 16057504953296608513249955)
                  ·
                    refine ⟨24086257429944912769874933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16057504953296608513249955 24086257429944912769874933)
                    ·
                      refine ⟨2258086634057335572175775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24086257429944912769874933 2258086634057335572175775)
                      ·
                        rfl

theorem cell23_4397608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4397608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397608 prefixEnd_4397608 := by exact prefixLift 4397608
  have htrace : WordTrace (prefixWord ++ tailWord_4397608) baseStart_4397608 baseEnd_4397608 := by
    simpa [prefixWord, tailWord_4397608, baseEnd_4397608] using wordTrace_append hprefix tailTrace_4397608
  have hstable : (prefixWord ++ tailWord_4397608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397608).length < 2 ^ (prefixWord ++ tailWord_4397608).sum := by decide
  have hdescent : baseEnd_4397608 < baseStart_4397608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397622 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_4397622 : Nat := 118140960795 + 4397622 * 2 ^ 59
def prefixEnd_4397622 : Nat := 4983230072969 + 3 ^ 40 * 4397622 * 2
def baseEnd_4397622 : Nat := 2258093822786498517400711

theorem tailTrace_4397622 : CollatzResearch.WordTrace tailWord_4397622 prefixEnd_4397622 2258093822786498517400711 := by
  unfold tailWord_4397622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10024653204635876430515195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106929634182782681925495413 10024653204635876430515195)
  ·
    refine ⟨15036979806953814645772793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10024653204635876430515195 15036979806953814645772793)
    ·
      refine ⟨11277734855215360984329595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15036979806953814645772793 11277734855215360984329595)
      ·
        refine ⟨16916602282823041476494393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11277734855215360984329595 16916602282823041476494393)
        ·
          refine ⟨12687451712117281107370795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16916602282823041476494393 12687451712117281107370795)
          ·
            refine ⟨19031177568175921661056193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12687451712117281107370795 19031177568175921661056193)
            ·
              refine ⟨14273383176131941245792145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19031177568175921661056193 14273383176131941245792145)
              ·
                refine ⟨10705037382098955934344109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14273383176131941245792145 10705037382098955934344109)
                ·
                  refine ⟨4014389018287108475379041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10705037382098955934344109 4014389018287108475379041)
                  ·
                    refine ⟨3010791763715331356534281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4014389018287108475379041 3010791763715331356534281)
                    ·
                      refine ⟨2258093822786498517400711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010791763715331356534281 2258093822786498517400711)
                      ·
                        rfl

theorem cell23_4397622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_4397622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397622 prefixEnd_4397622 := by exact prefixLift 4397622
  have htrace : WordTrace (prefixWord ++ tailWord_4397622) baseStart_4397622 baseEnd_4397622 := by
    simpa [prefixWord, tailWord_4397622, baseEnd_4397622] using wordTrace_append hprefix tailTrace_4397622
  have hstable : (prefixWord ++ tailWord_4397622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397622).length < 2 ^ (prefixWord ++ tailWord_4397622).sum := by decide
  have hdescent : baseEnd_4397622 < baseStart_4397622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397628 : List Nat := [2, 2, 2, 2, 3, 3, 2, 7]
def baseStart_4397628 : Nat := 118140960795 + 4397628 * 2 ^ 59
def prefixEnd_4397628 : Nat := 4983230072969 + 3 ^ 40 * 4397628 * 2
def baseEnd_4397628 : Nat := 83633218654460203478729

theorem tailTrace_4397628 : CollatzResearch.WordTrace tailWord_4397628 prefixEnd_4397628 83633218654460203478729 := by
  unfold tailWord_4397628
  simp only [CollatzResearch.WordTrace]
  refine ⟨80197335056076142956480769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106929780074768190608641025 80197335056076142956480769)
  ·
    refine ⟨60148001292057107217360577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80197335056076142956480769 60148001292057107217360577)
    ·
      refine ⟨45111000969042830413020433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60148001292057107217360577 45111000969042830413020433)
      ·
        refine ⟨33833250726782122809765325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45111000969042830413020433 33833250726782122809765325)
        ·
          refine ⟨12687469022543296053661997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33833250726782122809765325 12687469022543296053661997)
          ·
            refine ⟨4757800883453736020123249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12687469022543296053661997 4757800883453736020123249)
            ·
              refine ⟨3568350662590302015092437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4757800883453736020123249 3568350662590302015092437)
              ·
                refine ⟨83633218654460203478729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3568350662590302015092437 83633218654460203478729)
                ·
                  rfl

theorem cell23_4397628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 7].length) (baseStart_4397628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397628 prefixEnd_4397628 := by exact prefixLift 4397628
  have htrace : WordTrace (prefixWord ++ tailWord_4397628) baseStart_4397628 baseEnd_4397628 := by
    simpa [prefixWord, tailWord_4397628, baseEnd_4397628] using wordTrace_append hprefix tailTrace_4397628
  have hstable : (prefixWord ++ tailWord_4397628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397628).length < 2 ^ (prefixWord ++ tailWord_4397628).sum := by decide
  have hdescent : baseEnd_4397628 < baseStart_4397628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397639 : List Nat := [1, 1, 4, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_4397639 : Nat := 118140960795 + 4397639 * 2 ^ 59
def prefixEnd_4397639 : Nat := 4983230072969 + 3 ^ 40 * 4397639 * 2
def baseEnd_4397639 : Nat := 2258102551957624950888133

theorem tailTrace_4397639 : CollatzResearch.WordTrace tailWord_4397639 prefixEnd_4397639 2258102551957624950888133 := by
  unfold tailWord_4397639
  simp only [CollatzResearch.WordTrace]
  refine ⟨160395071315112434791611971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106930047543408289861074647 160395071315112434791611971)
  ·
    refine ⟨240592606972668652187417957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160395071315112434791611971 240592606972668652187417957)
    ·
      refine ⟨45111113807375372285140867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240592606972668652187417957 45111113807375372285140867)
      ·
        refine ⟨67666670711063058427711301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45111113807375372285140867 67666670711063058427711301)
        ·
          refine ⟨12687500758324323455195869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67666670711063058427711301 12687500758324323455195869)
          ·
            refine ⟨4757812784371621295698451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12687500758324323455195869 4757812784371621295698451)
            ·
              refine ⟨7136719176557431943547677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757812784371621295698451 7136719176557431943547677)
              ·
                refine ⟨2676269691209036978830379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7136719176557431943547677 2676269691209036978830379)
                ·
                  refine ⟨4014404536813555468245569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676269691209036978830379 4014404536813555468245569)
                  ·
                    refine ⟨3010803402610166601184177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4014404536813555468245569 3010803402610166601184177)
                    ·
                      refine ⟨2258102551957624950888133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010803402610166601184177 2258102551957624950888133)
                      ·
                        rfl

theorem cell23_4397639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_4397639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397639 prefixEnd_4397639 := by exact prefixLift 4397639
  have htrace : WordTrace (prefixWord ++ tailWord_4397639) baseStart_4397639 baseEnd_4397639 := by
    simpa [prefixWord, tailWord_4397639, baseEnd_4397639] using wordTrace_append hprefix tailTrace_4397639
  have hstable : (prefixWord ++ tailWord_4397639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397639).length < 2 ^ (prefixWord ++ tailWord_4397639).sum := by decide
  have hdescent : baseEnd_4397639 < baseStart_4397639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397662 : List Nat := [4, 4, 1, 2, 1, 1, 2, 8]
def baseStart_4397662 : Nat := 118140960795 + 4397662 * 2 ^ 59
def prefixEnd_4397662 : Nat := 4983230072969 + 3 ^ 40 * 4397662 * 2
def baseEnd_4397662 : Nat := 83633865259728828181501

theorem tailTrace_4397662 : CollatzResearch.WordTrace tailWord_4397662 prefixEnd_4397662 83633865259728828181501 := by
  unfold tailWord_4397662
  simp only [CollatzResearch.WordTrace]
  refine ⟨20049488774253638714962405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106930606796019406479799493 20049488774253638714962405)
  ·
    refine ⟨3759279145172557259055451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20049488774253638714962405 3759279145172557259055451)
    ·
      refine ⟨5638918717758835888583177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3759279145172557259055451 5638918717758835888583177)
      ·
        refine ⟨4229189038319126916437383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5638918717758835888583177 4229189038319126916437383)
        ·
          refine ⟨6343783557478690374656075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4229189038319126916437383 6343783557478690374656075)
          ·
            refine ⟨9515675336218035561984113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343783557478690374656075 9515675336218035561984113)
            ·
              refine ⟨7136756502163526671488085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9515675336218035561984113 7136756502163526671488085)
              ·
                refine ⟨83633865259728828181501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7136756502163526671488085 83633865259728828181501)
                ·
                  rfl

theorem cell23_4397662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_4397662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397662 prefixEnd_4397662 := by exact prefixLift 4397662
  have htrace : WordTrace (prefixWord ++ tailWord_4397662) baseStart_4397662 baseEnd_4397662 := by
    simpa [prefixWord, tailWord_4397662, baseEnd_4397662] using wordTrace_append hprefix tailTrace_4397662
  have hstable : (prefixWord ++ tailWord_4397662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397662).length < 2 ^ (prefixWord ++ tailWord_4397662).sum := by decide
  have hdescent : baseEnd_4397662 < baseStart_4397662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397666 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_4397666 : Nat := 118140960795 + 4397666 * 2 ^ 59
def prefixEnd_4397666 : Nat := 4983230072969 + 3 ^ 40 * 4397666 * 2
def baseEnd_4397666 : Nat := 752705471978432115083503

theorem tailTrace_4397666 : CollatzResearch.WordTrace tailWord_4397666 prefixEnd_4397666 752705471978432115083503 := by
  unfold tailWord_4397666
  simp only [CollatzResearch.WordTrace]
  refine ⟨40099014021503654600711213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106930704057343078935229901 40099014021503654600711213)
  ·
    refine ⟨15037130258063870475266705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40099014021503654600711213 15037130258063870475266705)
    ·
      refine ⟨11277847693547902856450029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15037130258063870475266705 11277847693547902856450029)
      ·
        refine ⟨4229192885080463571168761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11277847693547902856450029 4229192885080463571168761)
        ·
          refine ⟨3171894663810347678376571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4229192885080463571168761 3171894663810347678376571)
          ·
            refine ⟨4757841995715521517564857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171894663810347678376571 4757841995715521517564857)
            ·
              refine ⟨3568381496786641138173643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4757841995715521517564857 3568381496786641138173643)
              ·
                refine ⟨5352572245179961707260465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3568381496786641138173643 5352572245179961707260465)
                ·
                  refine ⟨4014429183884971280445349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5352572245179961707260465 4014429183884971280445349)
                  ·
                    refine ⟨752705471978432115083503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4014429183884971280445349 752705471978432115083503)
                    ·
                      rfl

theorem cell23_4397666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_4397666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397666 prefixEnd_4397666 := by exact prefixLift 4397666
  have htrace : WordTrace (prefixWord ++ tailWord_4397666) baseStart_4397666 baseEnd_4397666 := by
    simpa [prefixWord, tailWord_4397666, baseEnd_4397666] using wordTrace_append hprefix tailTrace_4397666
  have hstable : (prefixWord ++ tailWord_4397666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397666).length < 2 ^ (prefixWord ++ tailWord_4397666).sum := by decide
  have hdescent : baseEnd_4397666 < baseStart_4397666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397672 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4397672 : Nat := 118140960795 + 4397672 * 2 ^ 59
def prefixEnd_4397672 : Nat := 4983230072969 + 3 ^ 40 * 4397672 * 2
def baseEnd_4397672 : Nat := 2258119496819223321775481

theorem tailTrace_4397672 : CollatzResearch.WordTrace tailWord_4397672 prefixEnd_4397672 2258119496819223321775481 := by
  unfold tailWord_4397672
  simp only [CollatzResearch.WordTrace]
  refine ⟨80198137461996440713781635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106930849949328587618375513 80198137461996440713781635)
  ·
    refine ⟨120297206192994661070672453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80198137461996440713781635 120297206192994661070672453)
    ·
      refine ⟨22555726161186498950751085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120297206192994661070672453 22555726161186498950751085)
      ·
        refine ⟨8458397310444937106531657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22555726161186498950751085 8458397310444937106531657)
        ·
          refine ⟨6343797982833702829898743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8458397310444937106531657 6343797982833702829898743)
          ·
            refine ⟨9515696974250554244848115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343797982833702829898743 9515696974250554244848115)
            ·
              refine ⟨14273545461375831367272173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9515696974250554244848115 14273545461375831367272173)
              ·
                refine ⟨5352579548015936762727065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14273545461375831367272173 5352579548015936762727065)
                ·
                  refine ⟨4014434661011952572045299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5352579548015936762727065 4014434661011952572045299)
                  ·
                    refine ⟨6021651991517928858067949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4014434661011952572045299 6021651991517928858067949)
                    ·
                      refine ⟨2258119496819223321775481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021651991517928858067949 2258119496819223321775481)
                      ·
                        rfl

theorem cell23_4397672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4397672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397672 prefixEnd_4397672 := by exact prefixLift 4397672
  have htrace : WordTrace (prefixWord ++ tailWord_4397672) baseStart_4397672 baseEnd_4397672 := by
    simpa [prefixWord, tailWord_4397672, baseEnd_4397672] using wordTrace_append hprefix tailTrace_4397672
  have hstable : (prefixWord ++ tailWord_4397672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397672).length < 2 ^ (prefixWord ++ tailWord_4397672).sum := by decide
  have hdescent : baseEnd_4397672 < baseStart_4397672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 3]
def baseStart_4397711 : Nat := 118140960795 + 4397711 * 2 ^ 59
def prefixEnd_4397711 : Nat := 4983230072969 + 3 ^ 40 * 4397711 * 2
def baseEnd_4397711 : Nat := 2258139522564748669187801

theorem tailTrace_4397711 : CollatzResearch.WordTrace tailWord_4397711 prefixEnd_4397711 2258139522564748669187801 := by
  unfold tailWord_4397711
  simp only [CollatzResearch.WordTrace]
  refine ⟨160397697370851591088232987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106931798247234394058821991 160397697370851591088232987)
  ·
    refine ⟨240596546056277386632349481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160397697370851591088232987 240596546056277386632349481)
    ·
      refine ⟨180447409542208039974262111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240596546056277386632349481 180447409542208039974262111)
      ·
        refine ⟨270671114313312059961393167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180447409542208039974262111 270671114313312059961393167)
        ·
          refine ⟨406006671469968089942089751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270671114313312059961393167 406006671469968089942089751)
          ·
            refine ⟨609010007204952134913134627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406006671469968089942089751 609010007204952134913134627)
            ·
              refine ⟨913515010807428202369701941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609010007204952134913134627 913515010807428202369701941)
              ·
                refine ⟨85642032263196393972159557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 913515010807428202369701941 85642032263196393972159557)
                ·
                  refine ⟨16057881049349323869779917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85642032263196393972159557 16057881049349323869779917)
                  ·
                    refine ⟨6021705393505996451167469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16057881049349323869779917 6021705393505996451167469)
                    ·
                      refine ⟨2258139522564748669187801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021705393505996451167469 2258139522564748669187801)
                      ·
                        rfl

theorem cell23_4397711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_4397711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397711 prefixEnd_4397711 := by exact prefixLift 4397711
  have htrace : WordTrace (prefixWord ++ tailWord_4397711) baseStart_4397711 baseEnd_4397711 := by
    simpa [prefixWord, tailWord_4397711, baseEnd_4397711] using wordTrace_append hprefix tailTrace_4397711
  have hstable : (prefixWord ++ tailWord_4397711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397711).length < 2 ^ (prefixWord ++ tailWord_4397711).sum := by decide
  have hdescent : baseEnd_4397711 < baseStart_4397711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397735 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 7]
def baseStart_4397735 : Nat := 118140960795 + 4397735 * 2 ^ 59
def prefixEnd_4397735 : Nat := 4983230072969 + 3 ^ 40 * 4397735 * 2
def baseEnd_4397735 : Nat := 250905760677828508365299

theorem tailTrace_4397735 : CollatzResearch.WordTrace tailWord_4397735 prefixEnd_4397735 250905760677828508365299 := by
  unfold tailWord_4397735
  simp only [CollatzResearch.WordTrace]
  refine ⟨160398572722764643187106659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106932381815176428791404439 160398572722764643187106659)
  ·
    refine ⟨240597859084146964780659989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160398572722764643187106659 240597859084146964780659989)
    ·
      refine ⟨11278024644569388974093437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 240597859084146964780659989 11278024644569388974093437)
      ·
        refine ⟨4229259241713520865285039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11278024644569388974093437 4229259241713520865285039)
        ·
          refine ⟨6343888862570281297927559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4229259241713520865285039 6343888862570281297927559)
          ·
            refine ⟨9515833293855421946891339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343888862570281297927559 9515833293855421946891339)
            ·
              refine ⟨14273749940783132920337009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9515833293855421946891339 14273749940783132920337009)
              ·
                refine ⟨10705312455587349690252757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14273749940783132920337009 10705312455587349690252757)
                ·
                  refine ⟨250905760677828508365299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10705312455587349690252757 250905760677828508365299)
                  ·
                    rfl

theorem cell23_4397735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 7].length) (baseStart_4397735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397735 prefixEnd_4397735 := by exact prefixLift 4397735
  have htrace : WordTrace (prefixWord ++ tailWord_4397735) baseStart_4397735 baseEnd_4397735 := by
    simpa [prefixWord, tailWord_4397735, baseEnd_4397735] using wordTrace_append hprefix tailTrace_4397735
  have hstable : (prefixWord ++ tailWord_4397735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397735).length < 2 ^ (prefixWord ++ tailWord_4397735).sum := by decide
  have hdescent : baseEnd_4397735 < baseStart_4397735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397795 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 3, 4]
def baseStart_4397795 : Nat := 118140960795 + 4397795 * 2 ^ 59
def prefixEnd_4397795 : Nat := 4983230072969 + 3 ^ 40 * 4397795 * 2
def baseEnd_4397795 : Nat := 752727551646575446845805

theorem tailTrace_4397795 : CollatzResearch.WordTrace tailWord_4397795 prefixEnd_4397795 752727551646575446845805 := by
  unfold tailWord_4397795
  simp only [CollatzResearch.WordTrace]
  refine ⟨160400761102547273434290839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106933840735031515622860559 160400761102547273434290839)
  ·
    refine ⟨240601141653820910151436259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160400761102547273434290839 240601141653820910151436259)
    ·
      refine ⟨360901712480731365227154389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240601141653820910151436259 360901712480731365227154389)
      ·
        refine ⟨8458633886267141372511431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 360901712480731365227154389 8458633886267141372511431)
        ·
          refine ⟨12687950829400712058767147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8458633886267141372511431 12687950829400712058767147)
          ·
            refine ⟨19031926244101068088150721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12687950829400712058767147 19031926244101068088150721)
            ·
              refine ⟨14273944683075801066113041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19031926244101068088150721 14273944683075801066113041)
              ·
                refine ⟨10705458512306850799584781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14273944683075801066113041 10705458512306850799584781)
                ·
                  refine ⟨4014546942115069049844293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10705458512306850799584781 4014546942115069049844293)
                  ·
                    refine ⟨752727551646575446845805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4014546942115069049844293 752727551646575446845805)
                    ·
                      rfl

theorem cell23_4397795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 4].length) (baseStart_4397795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397795 prefixEnd_4397795 := by exact prefixLift 4397795
  have htrace : WordTrace (prefixWord ++ tailWord_4397795) baseStart_4397795 baseEnd_4397795 := by
    simpa [prefixWord, tailWord_4397795, baseEnd_4397795] using wordTrace_append hprefix tailTrace_4397795
  have hstable : (prefixWord ++ tailWord_4397795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397795).length < 2 ^ (prefixWord ++ tailWord_4397795).sum := by decide
  have hdescent : baseEnd_4397795 < baseStart_4397795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397805 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4397805 : Nat := 118140960795 + 4397805 * 2 ^ 59
def prefixEnd_4397805 : Nat := 4983230072969 + 3 ^ 40 * 4397805 * 2
def baseEnd_4397805 : Nat := 2258187789746271301412369

theorem tailTrace_4397805 : CollatzResearch.WordTrace tailWord_4397805 prefixEnd_4397805 2258187789746271301412369 := by
  unfold tailWord_4397805
  simp only [CollatzResearch.WordTrace]
  refine ⟨160401125832511045142154869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106934083888340696761436579 160401125832511045142154869)
  ·
    refine ⟨15037605546797910482077019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160401125832511045142154869 15037605546797910482077019)
    ·
      refine ⟨22556408320196865723115529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15037605546797910482077019 22556408320196865723115529)
      ·
        refine ⟨16917306240147649292336647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22556408320196865723115529 16917306240147649292336647)
        ·
          refine ⟨25375959360221473938504971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16917306240147649292336647 25375959360221473938504971)
          ·
            refine ⟨38063939040332210907757457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25375959360221473938504971 38063939040332210907757457)
            ·
              refine ⟨28547954280249158180818093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38063939040332210907757457 28547954280249158180818093)
              ·
                refine ⟨10705482855093434317806785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28547954280249158180818093 10705482855093434317806785)
                ·
                  refine ⟨8029112141320075738355089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10705482855093434317806785 8029112141320075738355089)
                  ·
                    refine ⟨6021834105990056803766317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8029112141320075738355089 6021834105990056803766317)
                    ·
                      refine ⟨2258187789746271301412369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021834105990056803766317 2258187789746271301412369)
                      ·
                        rfl

theorem cell23_4397805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4397805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397805 prefixEnd_4397805 := by exact prefixLift 4397805
  have htrace : WordTrace (prefixWord ++ tailWord_4397805) baseStart_4397805 baseEnd_4397805 := by
    simpa [prefixWord, tailWord_4397805, baseEnd_4397805] using wordTrace_append hprefix tailTrace_4397805
  have hstable : (prefixWord ++ tailWord_4397805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397805).length < 2 ^ (prefixWord ++ tailWord_4397805).sum := by decide
  have hdescent : baseEnd_4397805 < baseStart_4397805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397822 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_4397822 : Nat := 118140960795 + 4397822 * 2 ^ 59
def prefixEnd_4397822 : Nat := 4983230072969 + 3 ^ 40 * 4397822 * 2
def baseEnd_4397822 : Nat := 2258196518917397734899791

theorem tailTrace_4397822 : CollatzResearch.WordTrace tailWord_4397822 prefixEnd_4397822 2258196518917397734899791 := by
  unfold tailWord_4397822
  simp only [CollatzResearch.WordTrace]
  refine ⟨20050218234181182130690465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106934497248966304697015813 20050218234181182130690465)
  ·
    refine ⟨15037663675635886598017849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20050218234181182130690465 15037663675635886598017849)
    ·
      refine ⟨11278247756726914948513387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15037663675635886598017849 11278247756726914948513387)
      ·
        refine ⟨16917371635090372422770081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11278247756726914948513387 16917371635090372422770081)
        ·
          refine ⟨12688028726317779317077561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16917371635090372422770081 12688028726317779317077561)
          ·
            refine ⟨9516021544738334487808171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12688028726317779317077561 9516021544738334487808171)
            ·
              refine ⟨14274032317107501731712257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9516021544738334487808171 14274032317107501731712257)
              ·
                refine ⟨10705524237830626298784193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14274032317107501731712257 10705524237830626298784193)
                ·
                  refine ⟨8029143178372969724088145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10705524237830626298784193 8029143178372969724088145)
                  ·
                    refine ⟨6021857383779727293066109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8029143178372969724088145 6021857383779727293066109)
                    ·
                      refine ⟨2258196518917397734899791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021857383779727293066109 2258196518917397734899791)
                      ·
                        rfl

theorem cell23_4397822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_4397822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397822 prefixEnd_4397822 := by exact prefixLift 4397822
  have htrace : WordTrace (prefixWord ++ tailWord_4397822) baseStart_4397822 baseEnd_4397822 := by
    simpa [prefixWord, tailWord_4397822, baseEnd_4397822] using wordTrace_append hprefix tailTrace_4397822
  have hstable : (prefixWord ++ tailWord_4397822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397822).length < 2 ^ (prefixWord ++ tailWord_4397822).sum := by decide
  have hdescent : baseEnd_4397822 < baseStart_4397822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397838 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_4397838 : Nat := 118140960795 + 4397838 * 2 ^ 59
def prefixEnd_4397838 : Nat := 4983230072969 + 3 ^ 40 * 4397838 * 2
def baseEnd_4397838 : Nat := 752734911535956557433239

theorem tailTrace_4397838 : CollatzResearch.WordTrace tailWord_4397838 prefixEnd_4397838 752734911535956557433239 := by
  unfold tailWord_4397838
  simp only [CollatzResearch.WordTrace]
  refine ⟨20050291180173936472263271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106934886294260994518737445 20050291180173936472263271)
  ·
    refine ⟨30075436770260904708394907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20050291180173936472263271 30075436770260904708394907)
    ·
      refine ⟨45113155155391357062592361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30075436770260904708394907 45113155155391357062592361)
      ·
        refine ⟨33834866366543517796944271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45113155155391357062592361 33834866366543517796944271)
        ·
          refine ⟨50752299549815276695416407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33834866366543517796944271 50752299549815276695416407)
          ·
            refine ⟨76128449324722915043124611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50752299549815276695416407 76128449324722915043124611)
            ·
              refine ⟨114192673987084372564686917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76128449324722915043124611 114192673987084372564686917)
              ·
                refine ⟨21411126372578319855878797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114192673987084372564686917 21411126372578319855878797)
                ·
                  refine ⟨8029172389716869945954549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21411126372578319855878797 8029172389716869945954549)
                  ·
                    refine ⟨752734911535956557433239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8029172389716869945954549 752734911535956557433239)
                    ·
                      rfl

theorem cell23_4397838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_4397838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397838 prefixEnd_4397838 := by exact prefixLift 4397838
  have htrace : WordTrace (prefixWord ++ tailWord_4397838) baseStart_4397838 baseEnd_4397838 := by
    simpa [prefixWord, tailWord_4397838, baseEnd_4397838] using wordTrace_append hprefix tailTrace_4397838
  have hstable : (prefixWord ++ tailWord_4397838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397838).length < 2 ^ (prefixWord ++ tailWord_4397838).sum := by decide
  have hdescent : baseEnd_4397838 < baseStart_4397838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397842 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 6]
def baseStart_4397842 : Nat := 118140960795 + 4397842 * 2 ^ 59
def prefixEnd_4397842 : Nat := 4983230072969 + 3 ^ 40 * 4397842 * 2
def baseEnd_4397842 : Nat := 250911865392276406294411

theorem tailTrace_4397842 : CollatzResearch.WordTrace tailWord_4397842 prefixEnd_4397842 250911865392276406294411 := by
  unfold tailWord_4397842
  simp only [CollatzResearch.WordTrace]
  refine ⟨40100618833344250115312945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106934983555584666974167853 40100618833344250115312945)
  ·
    refine ⟨30075464125008187586484709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40100618833344250115312945 30075464125008187586484709)
    ·
      refine ⟨5639149523439035172465883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30075464125008187586484709 5639149523439035172465883)
      ·
        refine ⟨8458724285158552758698825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5639149523439035172465883 8458724285158552758698825)
        ·
          refine ⟨6344043213868914569024119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8458724285158552758698825 6344043213868914569024119)
          ·
            refine ⟨9516064820803371853536179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6344043213868914569024119 9516064820803371853536179)
            ·
              refine ⟨14274097231205057780304269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9516064820803371853536179 14274097231205057780304269)
              ·
                refine ⟨5352786461701896667614101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14274097231205057780304269 5352786461701896667614101)
                ·
                  refine ⟨250911865392276406294411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5352786461701896667614101 250911865392276406294411)
                  ·
                    rfl

theorem cell23_4397842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_4397842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397842 prefixEnd_4397842 := by exact prefixLift 4397842
  have htrace : WordTrace (prefixWord ++ tailWord_4397842) baseStart_4397842 baseEnd_4397842 := by
    simpa [prefixWord, tailWord_4397842, baseEnd_4397842] using wordTrace_append hprefix tailTrace_4397842
  have hstable : (prefixWord ++ tailWord_4397842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397842).length < 2 ^ (prefixWord ++ tailWord_4397842).sum := by decide
  have hdescent : baseEnd_4397842 < baseStart_4397842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397845 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_4397845 : Nat := 118140960795 + 4397845 * 2 ^ 59
def prefixEnd_4397845 : Nat := 4983230072969 + 3 ^ 40 * 4397845 * 2
def baseEnd_4397845 : Nat := 2258208328972451144912185

theorem tailTrace_4397845 : CollatzResearch.WordTrace tailWord_4397845 prefixEnd_4397845 2258208328972451144912185 := by
  unfold tailWord_4397845
  simp only [CollatzResearch.WordTrace]
  refine ⟨160402584752366131973610989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106935056501577421315740659 160402584752366131973610989)
  ·
    refine ⟨60150969282137299490104121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160402584752366131973610989 60150969282137299490104121)
    ·
      refine ⟨45113226961602974617578091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60150969282137299490104121 45113226961602974617578091)
      ·
        refine ⟨67669840442404461926367137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45113226961602974617578091 67669840442404461926367137)
        ·
          refine ⟨50752380331803346444775353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67669840442404461926367137 50752380331803346444775353)
          ·
            refine ⟨38064285248852509833581515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50752380331803346444775353 38064285248852509833581515)
            ·
              refine ⟨57096427873278764750372273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38064285248852509833581515 57096427873278764750372273)
              ·
                refine ⟨42822320904959073562779205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57096427873278764750372273 42822320904959073562779205)
                ·
                  refine ⟨8029185169679826293021101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42822320904959073562779205 8029185169679826293021101)
                  ·
                    refine ⟨3010944438629934859882913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8029185169679826293021101 3010944438629934859882913)
                    ·
                      refine ⟨2258208328972451144912185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3010944438629934859882913 2258208328972451144912185)
                      ·
                        rfl

theorem cell23_4397845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_4397845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397845 prefixEnd_4397845 := by exact prefixLift 4397845
  have htrace : WordTrace (prefixWord ++ tailWord_4397845) baseStart_4397845 baseEnd_4397845 := by
    simpa [prefixWord, tailWord_4397845, baseEnd_4397845] using wordTrace_append hprefix tailTrace_4397845
  have hstable : (prefixWord ++ tailWord_4397845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397845).length < 2 ^ (prefixWord ++ tailWord_4397845).sum := by decide
  have hdescent : baseEnd_4397845 < baseStart_4397845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397855 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 1, 5]
def baseStart_4397855 : Nat := 118140960795 + 4397855 * 2 ^ 59
def prefixEnd_4397855 : Nat := 4983230072969 + 3 ^ 40 * 4397855 * 2
def baseEnd_4397855 : Nat := 752737821259665368595713

theorem tailTrace_4397855 : CollatzResearch.WordTrace tailWord_4397855 prefixEnd_4397855 752737821259665368595713 := by
  unfold tailWord_4397855
  simp only [CollatzResearch.WordTrace]
  refine ⟨160402949482329903681475019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106935299654886602454316679 160402949482329903681475019)
  ·
    refine ⟨240604424223494855522212529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160402949482329903681475019 240604424223494855522212529)
    ·
      refine ⟨180453318167621141641659397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240604424223494855522212529 180453318167621141641659397)
      ·
        refine ⟨33834997156428964057811137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180453318167621141641659397 33834997156428964057811137)
        ·
          refine ⟨25376247867321723043358353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33834997156428964057811137 25376247867321723043358353)
          ·
            refine ⟨19032185900491292282518765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25376247867321723043358353 19032185900491292282518765)
            ·
              refine ⟨7137069712684234605944537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19032185900491292282518765 7137069712684234605944537)
              ·
                refine ⟨5352802284513175954458403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7137069712684234605944537 5352802284513175954458403)
                ·
                  refine ⟨8029203426769763931687605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352802284513175954458403 8029203426769763931687605)
                  ·
                    refine ⟨752737821259665368595713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8029203426769763931687605 752737821259665368595713)
                    ·
                      rfl

theorem cell23_4397855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_4397855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397855 prefixEnd_4397855 := by exact prefixLift 4397855
  have htrace : WordTrace (prefixWord ++ tailWord_4397855) baseStart_4397855 baseEnd_4397855 := by
    simpa [prefixWord, tailWord_4397855, baseEnd_4397855] using wordTrace_append hprefix tailTrace_4397855
  have hstable : (prefixWord ++ tailWord_4397855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397855).length < 2 ^ (prefixWord ++ tailWord_4397855).sum := by decide
  have hdescent : baseEnd_4397855 < baseStart_4397855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397868 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_4397868 : Nat := 118140960795 + 4397868 * 2 ^ 59
def prefixEnd_4397868 : Nat := 4983230072969 + 3 ^ 40 * 4397868 * 2
def baseEnd_4397868 : Nat := 752740046342501518308193

theorem tailTrace_4397868 : CollatzResearch.WordTrace tailWord_4397868 prefixEnd_4397868 752740046342501518308193 := by
  unfold tailWord_4397868
  simp only [CollatzResearch.WordTrace]
  refine ⟨80201711815641403450849129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106935615754188537934465505 80201711815641403450849129)
  ·
    refine ⟨60151283861731052588136847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80201711815641403450849129 60151283861731052588136847)
    ·
      refine ⟨90226925792596578882205271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60151283861731052588136847 90226925792596578882205271)
      ·
        refine ⟨135340388688894868323307907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90226925792596578882205271 135340388688894868323307907)
        ·
          refine ⟨203010583033342302484961861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135340388688894868323307907 203010583033342302484961861)
          ·
            refine ⟨38064484318751681715930349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203010583033342302484961861 38064484318751681715930349)
            ·
              refine ⟨14274181619531880643473881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38064484318751681715930349 14274181619531880643473881)
              ·
                refine ⟨10705636214648910482605411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14274181619531880643473881 10705636214648910482605411)
                ·
                  refine ⟨16058454321973365723908117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10705636214648910482605411 16058454321973365723908117)
                  ·
                    refine ⟨752740046342501518308193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16058454321973365723908117 752740046342501518308193)
                    ·
                      rfl

theorem cell23_4397868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_4397868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397868 prefixEnd_4397868 := by exact prefixLift 4397868
  have htrace : WordTrace (prefixWord ++ tailWord_4397868) baseStart_4397868 baseEnd_4397868 := by
    simpa [prefixWord, tailWord_4397868, baseEnd_4397868] using wordTrace_append hprefix tailTrace_4397868
  have hstable : (prefixWord ++ tailWord_4397868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397868).length < 2 ^ (prefixWord ++ tailWord_4397868).sum := by decide
  have hdescent : baseEnd_4397868 < baseStart_4397868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397881 : List Nat := [1, 2, 1, 19]
def baseStart_4397881 : Nat := 118140960795 + 4397881 * 2 ^ 59
def prefixEnd_4397881 : Nat := 4983230072969 + 3 ^ 40 * 4397881 * 2
def baseEnd_4397881 : Nat := 1032568273560133975337

theorem tailTrace_4397881 : CollatzResearch.WordTrace tailWord_4397881 prefixEnd_4397881 1032568273560133975337 := by
  unfold tailWord_4397881
  simp only [CollatzResearch.WordTrace]
  refine ⟨160403897780235710121921497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106935931853490473414614331 160403897780235710121921497)
  ·
    refine ⟨120302923335176782591441123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160403897780235710121921497 120302923335176782591441123)
    ·
      refine ⟨180454385002765173887161685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120302923335176782591441123 180454385002765173887161685)
      ·
        refine ⟨1032568273560133975337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 19 180454385002765173887161685 1032568273560133975337)
        ·
          rfl

theorem cell23_4397881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 19].length) (baseStart_4397881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397881 prefixEnd_4397881 := by exact prefixLift 4397881
  have htrace : WordTrace (prefixWord ++ tailWord_4397881) baseStart_4397881 baseEnd_4397881 := by
    simpa [prefixWord, tailWord_4397881, baseEnd_4397881] using wordTrace_append hprefix tailTrace_4397881
  have hstable : (prefixWord ++ tailWord_4397881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397881).length < 2 ^ (prefixWord ++ tailWord_4397881).sum := by decide
  have hdescent : baseEnd_4397881 < baseStart_4397881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397886 : List Nat := [4, 2, 1, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_4397886 : Nat := 118140960795 + 4397886 * 2 ^ 59
def prefixEnd_4397886 : Nat := 4983230072969 + 3 ^ 40 * 4397886 * 2
def baseEnd_4397886 : Nat := 2258229381679285484499497

theorem tailTrace_4397886 : CollatzResearch.WordTrace tailWord_4397886 prefixEnd_4397886 2258229381679285484499497 := by
  unfold tailWord_4397886
  simp only [CollatzResearch.WordTrace]
  refine ⟨20050510018152199496981689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106936053430145063983902341 20050510018152199496981689)
  ·
    refine ⟨15037882513614149622736267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20050510018152199496981689 15037882513614149622736267)
    ·
      refine ⟨22556823770421224434104401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15037882513614149622736267 22556823770421224434104401)
      ·
        refine ⟨16917617827815918325578301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22556823770421224434104401 16917617827815918325578301)
        ·
          refine ⟨6344106685430969372091863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16917617827815918325578301 6344106685430969372091863)
          ·
            refine ⟨9516160028146454058137795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6344106685430969372091863 9516160028146454058137795)
            ·
              refine ⟨14274240042219681087206693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9516160028146454058137795 14274240042219681087206693)
              ·
                refine ⟨2676420007916190203851255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14274240042219681087206693 2676420007916190203851255)
                ·
                  refine ⟨4014630011874285305776883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676420007916190203851255 4014630011874285305776883)
                  ·
                    refine ⟨6021945017811427958665325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4014630011874285305776883 6021945017811427958665325)
                    ·
                      refine ⟨2258229381679285484499497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021945017811427958665325 2258229381679285484499497)
                      ·
                        rfl

theorem cell23_4397886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_4397886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397886 prefixEnd_4397886 := by exact prefixLift 4397886
  have htrace : WordTrace (prefixWord ++ tailWord_4397886) baseStart_4397886 baseEnd_4397886 := by
    simpa [prefixWord, tailWord_4397886, baseEnd_4397886] using wordTrace_append hprefix tailTrace_4397886
  have hstable : (prefixWord ++ tailWord_4397886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397886).length < 2 ^ (prefixWord ++ tailWord_4397886).sum := by decide
  have hdescent : baseEnd_4397886 < baseStart_4397886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397925 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_4397925 : Nat := 118140960795 + 4397925 * 2 ^ 59
def prefixEnd_4397925 : Nat := 4983230072969 + 3 ^ 40 * 4397925 * 2
def baseEnd_4397925 : Nat := 2258249407424810831911817

theorem tailTrace_4397925 : CollatzResearch.WordTrace tailWord_4397925 prefixEnd_4397925 2258249407424810831911817 := by
  unfold tailWord_4397925
  simp only [CollatzResearch.WordTrace]
  refine ⟨160405502592076305636523229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106937001728050870424348819 160405502592076305636523229)
  ·
    refine ⟨60152063472028614613696211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160405502592076305636523229 60152063472028614613696211)
    ·
      refine ⟨90228095208042921920544317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60152063472028614613696211 90228095208042921920544317)
      ·
        refine ⟨33835535703016095720204119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90228095208042921920544317 33835535703016095720204119)
        ·
          refine ⟨50753303554524143580306179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33835535703016095720204119 50753303554524143580306179)
          ·
            refine ⟨76129955331786215370459269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50753303554524143580306179 76129955331786215370459269)
            ·
              refine ⟨14274366624709915381961113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76129955331786215370459269 14274366624709915381961113)
              ·
                refine ⟨10705774968532436536470835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14274366624709915381961113 10705774968532436536470835)
                ·
                  refine ⟨16058662452798654804706253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10705774968532436536470835 16058662452798654804706253)
                  ·
                    refine ⟨6021998419799495551764845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16058662452798654804706253 6021998419799495551764845)
                    ·
                      refine ⟨2258249407424810831911817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6021998419799495551764845 2258249407424810831911817)
                      ·
                        rfl

theorem cell23_4397925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_4397925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397925 prefixEnd_4397925 := by exact prefixLift 4397925
  have htrace : WordTrace (prefixWord ++ tailWord_4397925) baseStart_4397925 baseEnd_4397925 := by
    simpa [prefixWord, tailWord_4397925, baseEnd_4397925] using wordTrace_append hprefix tailTrace_4397925
  have hstable : (prefixWord ++ tailWord_4397925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397925).length < 2 ^ (prefixWord ++ tailWord_4397925).sum := by decide
  have hdescent : baseEnd_4397925 < baseStart_4397925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397948 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_4397948 : Nat := 118140960795 + 4397948 * 2 ^ 59
def prefixEnd_4397948 : Nat := 4983230072969 + 3 ^ 40 * 4397948 * 2
def baseEnd_4397948 : Nat := 2258261217479864241924211

theorem tailTrace_4397948 : CollatzResearch.WordTrace tailWord_4397948 prefixEnd_4397948 2258261217479864241924211 := by
  unfold tailWord_4397948
  simp only [CollatzResearch.WordTrace]
  refine ⟨80203170735496490282305249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106937560980661987043073665 80203170735496490282305249)
  ·
    refine ⟨60152378051622367711728937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80203170735496490282305249 60152378051622367711728937)
    ·
      refine ⟨45114283538716775783796703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60152378051622367711728937 45114283538716775783796703)
      ·
        refine ⟨67671425308075163675695055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45114283538716775783796703 67671425308075163675695055)
        ·
          refine ⟨101507137962112745513542583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67671425308075163675695055 101507137962112745513542583)
          ·
            refine ⟨152260706943169118270313875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101507137962112745513542583 152260706943169118270313875)
            ·
              refine ⟨228391060414753677405470813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152260706943169118270313875 228391060414753677405470813)
              ·
                refine ⟨85646647655532629027051555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228391060414753677405470813 85646647655532629027051555)
                ·
                  refine ⟨128469971483298943540577333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85646647655532629027051555 128469971483298943540577333)
                  ·
                    refine ⟨12044059826559275956929125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 128469971483298943540577333 12044059826559275956929125)
                    ·
                      refine ⟨2258261217479864241924211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12044059826559275956929125 2258261217479864241924211)
                      ·
                        rfl

theorem cell23_4397948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_4397948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397948 prefixEnd_4397948 := by exact prefixLift 4397948
  have htrace : WordTrace (prefixWord ++ tailWord_4397948) baseStart_4397948 baseEnd_4397948 := by
    simpa [prefixWord, tailWord_4397948, baseEnd_4397948] using wordTrace_append hprefix tailTrace_4397948
  have hstable : (prefixWord ++ tailWord_4397948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397948).length < 2 ^ (prefixWord ++ tailWord_4397948).sum := by decide
  have hdescent : baseEnd_4397948 < baseStart_4397948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4397985 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4397985 : Nat := 118140960795 + 4397985 * 2 ^ 59
def prefixEnd_4397985 : Nat := 4983230072969 + 3 ^ 40 * 4397985 * 2
def baseEnd_4397985 : Nat := 2258280216264080597161541

theorem tailTrace_4397985 : CollatzResearch.WordTrace tailWord_4397985 prefixEnd_4397985 2258280216264080597161541 := by
  unfold tailWord_4397985
  simp only [CollatzResearch.WordTrace]
  refine ⟨160407690971858935883707409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106938460647905957255804939 160407690971858935883707409)
  ·
    refine ⟨120305768228894201912780557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160407690971858935883707409 120305768228894201912780557)
    ·
      refine ⟨45114663085835325717292709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120305768228894201912780557 45114663085835325717292709)
      ·
        refine ⟨8458999328594123571992383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45114663085835325717292709 8458999328594123571992383)
        ·
          refine ⟨12688498992891185357988575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8458999328594123571992383 12688498992891185357988575)
          ·
            refine ⟨19032748489336778036982863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12688498992891185357988575 19032748489336778036982863)
            ·
              refine ⟨28549122734005167055474295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19032748489336778036982863 28549122734005167055474295)
              ·
                refine ⟨42823684101007750583211443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28549122734005167055474295 42823684101007750583211443)
                ·
                  refine ⟨64235526151511625874817165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42823684101007750583211443 64235526151511625874817165)
                  ·
                    refine ⟨24088322306816859703056437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64235526151511625874817165 24088322306816859703056437)
                    ·
                      refine ⟨2258280216264080597161541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24088322306816859703056437 2258280216264080597161541)
                      ·
                        rfl

theorem cell23_4397985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4397985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4397985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4397985 prefixEnd_4397985 := by exact prefixLift 4397985
  have htrace : WordTrace (prefixWord ++ tailWord_4397985) baseStart_4397985 baseEnd_4397985 := by
    simpa [prefixWord, tailWord_4397985, baseEnd_4397985] using wordTrace_append hprefix tailTrace_4397985
  have hstable : (prefixWord ++ tailWord_4397985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4397985).length < 2 ^ (prefixWord ++ tailWord_4397985).sum := by decide
  have hdescent : baseEnd_4397985 < baseStart_4397985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4397985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398016 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 2, 2, 2]
def baseStart_4398016 : Nat := 118140960795 + 4398016 * 2 ^ 59
def prefixEnd_4398016 : Nat := 4983230072969 + 3 ^ 40 * 4398016 * 2
def baseEnd_4398016 : Nat := 2258296134164369975873899

theorem tailTrace_4398016 : CollatzResearch.WordTrace tailWord_4398016 prefixEnd_4398016 2258296134164369975873899 := by
  unfold tailWord_4398016
  simp only [CollatzResearch.WordTrace]
  refine ⟨80204410817373314089042951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106939214423164418785390601 80204410817373314089042951)
  ·
    refine ⟨120306616226059971133564427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80204410817373314089042951 120306616226059971133564427)
    ·
      refine ⟨180459924339089956700346641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120306616226059971133564427 180459924339089956700346641)
      ·
        refine ⟨135344943254317467525259981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180459924339089956700346641 135344943254317467525259981)
        ·
          refine ⟨50754353720369050321972493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135344943254317467525259981 50754353720369050321972493)
          ·
            refine ⟨19032882645138393870739685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50754353720369050321972493 19032882645138393870739685)
            ·
              refine ⟨3568665495963448850763691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19032882645138393870739685 3568665495963448850763691)
              ·
                refine ⟨5352998243945173276145537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3568665495963448850763691 5352998243945173276145537)
                ·
                  refine ⟨4014748682958879957109153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5352998243945173276145537 4014748682958879957109153)
                  ·
                    refine ⟨3011061512219159967831865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4014748682958879957109153 3011061512219159967831865)
                    ·
                      refine ⟨2258296134164369975873899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011061512219159967831865 2258296134164369975873899)
                      ·
                        rfl

theorem cell23_4398016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_4398016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398016 prefixEnd_4398016 := by exact prefixLift 4398016
  have htrace : WordTrace (prefixWord ++ tailWord_4398016) baseStart_4398016 baseEnd_4398016 := by
    simpa [prefixWord, tailWord_4398016, baseEnd_4398016] using wordTrace_append hprefix tailTrace_4398016
  have hstable : (prefixWord ++ tailWord_4398016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398016).length < 2 ^ (prefixWord ++ tailWord_4398016).sum := by decide
  have hdescent : baseEnd_4398016 < baseStart_4398016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398020 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_4398020 : Nat := 118140960795 + 4398020 * 2 ^ 59
def prefixEnd_4398020 : Nat := 4983230072969 + 3 ^ 40 * 4398020 * 2
def baseEnd_4398020 : Nat := 2258298188086987960223881

theorem tailTrace_4398020 : CollatzResearch.WordTrace tailWord_4398020 prefixEnd_4398020 2258298188086987960223881 := by
  unfold tailWord_4398020
  simp only [CollatzResearch.WordTrace]
  refine ⟨80204483763366068430615757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106939311684488091240821009 80204483763366068430615757)
  ·
    refine ⟨30076681411262275661480909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80204483763366068430615757 30076681411262275661480909)
    ·
      refine ⟨11278755529223353373055341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30076681411262275661480909 11278755529223353373055341)
      ·
        refine ⟨4229533323458757514895753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11278755529223353373055341 4229533323458757514895753)
        ·
          refine ⟨3172149992594068136171815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4229533323458757514895753 3172149992594068136171815)
          ·
            refine ⟨4758224988891102204257723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3172149992594068136171815 4758224988891102204257723)
            ·
              refine ⟨7137337483336653306386585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4758224988891102204257723 7137337483336653306386585)
              ·
                refine ⟨5353003112502489979789939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7137337483336653306386585 5353003112502489979789939)
                ·
                  refine ⟨8029504668753734969684909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5353003112502489979789939 8029504668753734969684909)
                  ·
                    refine ⟨3011064250782650613631841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8029504668753734969684909 3011064250782650613631841)
                    ·
                      refine ⟨2258298188086987960223881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011064250782650613631841 2258298188086987960223881)
                      ·
                        rfl

theorem cell23_4398020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_4398020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398020 prefixEnd_4398020 := by exact prefixLift 4398020
  have htrace : WordTrace (prefixWord ++ tailWord_4398020) baseStart_4398020 baseEnd_4398020 := by
    simpa [prefixWord, tailWord_4398020, baseEnd_4398020] using wordTrace_append hprefix tailTrace_4398020
  have hstable : (prefixWord ++ tailWord_4398020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398020).length < 2 ^ (prefixWord ++ tailWord_4398020).sum := by decide
  have hdescent : baseEnd_4398020 < baseStart_4398020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398075 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 3]
def baseStart_4398075 : Nat := 118140960795 + 4398075 * 2 ^ 59
def prefixEnd_4398075 : Nat := 4983230072969 + 3 ^ 40 * 4398075 * 2
def baseEnd_4398075 : Nat := 2258326429522985245036127

theorem tailTrace_4398075 : CollatzResearch.WordTrace tailWord_4398075 prefixEnd_4398075 2258326429522985245036127 := by
  unfold tailWord_4398075
  simp only [CollatzResearch.WordTrace]
  refine ⟨160410973541532881254483679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106940649027688587502989119 160410973541532881254483679)
  ·
    refine ⟨240616460312299321881725519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160410973541532881254483679 240616460312299321881725519)
    ·
      refine ⟨360924690468448982822588279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240616460312299321881725519 360924690468448982822588279)
      ·
        refine ⟨541387035702673474233882419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360924690468448982822588279 541387035702673474233882419)
        ·
          refine ⟨812080553554010211350823629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541387035702673474233882419 812080553554010211350823629)
          ·
            refine ⟨304530207582753829256558861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 812080553554010211350823629 304530207582753829256558861)
            ·
              refine ⟨114198827843532685971209573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 304530207582753829256558861 114198827843532685971209573)
              ·
                refine ⟨21412280220662378619601795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114198827843532685971209573 21412280220662378619601795)
                ·
                  refine ⟨32118420330993567929402693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21412280220662378619601795 32118420330993567929402693)
                  ·
                    refine ⟨6022203812061293986763005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32118420330993567929402693 6022203812061293986763005)
                    ·
                      refine ⟨2258326429522985245036127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6022203812061293986763005 2258326429522985245036127)
                      ·
                        rfl

theorem cell23_4398075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 3].length) (baseStart_4398075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398075 prefixEnd_4398075 := by exact prefixLift 4398075
  have htrace : WordTrace (prefixWord ++ tailWord_4398075) baseStart_4398075 baseEnd_4398075 := by
    simpa [prefixWord, tailWord_4398075, baseEnd_4398075] using wordTrace_append hprefix tailTrace_4398075
  have hstable : (prefixWord ++ tailWord_4398075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398075).length < 2 ^ (prefixWord ++ tailWord_4398075).sum := by decide
  have hdescent : baseEnd_4398075 < baseStart_4398075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398092 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_4398092 : Nat := 118140960795 + 4398092 * 2 ^ 59
def prefixEnd_4398092 : Nat := 4983230072969 + 3 ^ 40 * 4398092 * 2
def baseEnd_4398092 : Nat := 2258335158694111678523549

theorem tailTrace_4398092 : CollatzResearch.WordTrace tailWord_4398092 prefixEnd_4398092 2258335158694111678523549 := by
  unfold tailWord_4398092
  simp only [CollatzResearch.WordTrace]
  refine ⟨80205796791235646578926265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106941062388314195438568353 80205796791235646578926265)
  ·
    refine ⟨60154347593426734934194699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80205796791235646578926265 60154347593426734934194699)
    ·
      refine ⟨90231521390140102401292049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60154347593426734934194699 90231521390140102401292049)
      ·
        refine ⟨67673641042605076800969037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90231521390140102401292049 67673641042605076800969037)
        ·
          refine ⟨25377615390976903800363389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67673641042605076800969037 25377615390976903800363389)
          ·
            refine ⟨9516605771616338925136271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25377615390976903800363389 9516605771616338925136271)
            ·
              refine ⟨14274908657424508387704407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9516605771616338925136271 14274908657424508387704407)
              ·
                refine ⟨21412362986136762581556611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14274908657424508387704407 21412362986136762581556611)
                ·
                  refine ⟨32118544479205143872334917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21412362986136762581556611 32118544479205143872334917)
                  ·
                    refine ⟨6022227089850964476062797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32118544479205143872334917 6022227089850964476062797)
                    ·
                      refine ⟨2258335158694111678523549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6022227089850964476062797 2258335158694111678523549)
                      ·
                        rfl

theorem cell23_4398092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_4398092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398092 prefixEnd_4398092 := by exact prefixLift 4398092
  have htrace : WordTrace (prefixWord ++ tailWord_4398092) baseStart_4398092 baseEnd_4398092 := by
    simpa [prefixWord, tailWord_4398092, baseEnd_4398092] using wordTrace_append hprefix tailTrace_4398092
  have hstable : (prefixWord ++ tailWord_4398092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398092).length < 2 ^ (prefixWord ++ tailWord_4398092).sum := by decide
  have hdescent : baseEnd_4398092 < baseStart_4398092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398115 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6]
def baseStart_4398115 : Nat := 118140960795 + 4398115 * 2 ^ 59
def prefixEnd_4398115 : Nat := 4983230072969 + 3 ^ 40 * 4398115 * 2
def baseEnd_4398115 : Nat := 2258346968749165088535943

theorem tailTrace_4398115 : CollatzResearch.WordTrace tailWord_4398115 prefixEnd_4398115 2258346968749165088535943 := by
  unfold tailWord_4398115
  simp only [CollatzResearch.WordTrace]
  refine ⟨160412432461387968085939799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106941621640925312057293199 160412432461387968085939799)
  ·
    refine ⟨240618648692081952128909699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160412432461387968085939799 240618648692081952128909699)
    ·
      refine ⟨360927973038122928193364549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240618648692081952128909699 360927973038122928193364549)
      ·
        refine ⟨67673994944648049036255853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360927973038122928193364549 67673994944648049036255853)
        ·
          refine ⟨25377748104243018388595945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67673994944648049036255853 25377748104243018388595945)
          ·
            refine ⟨19033311078182263791446959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25377748104243018388595945 19033311078182263791446959)
            ·
              refine ⟨28549966617273395687170439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19033311078182263791446959 28549966617273395687170439)
              ·
                refine ⟨42824949925910093530755659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28549966617273395687170439 42824949925910093530755659)
                ·
                  refine ⟨64237424888865140296133489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42824949925910093530755659 64237424888865140296133489)
                  ·
                    refine ⟨48178068666648855222100117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64237424888865140296133489 48178068666648855222100117)
                    ·
                      refine ⟨2258346968749165088535943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48178068666648855222100117 2258346968749165088535943)
                      ·
                        rfl

theorem cell23_4398115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_4398115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398115 prefixEnd_4398115 := by exact prefixLift 4398115
  have htrace : WordTrace (prefixWord ++ tailWord_4398115) baseStart_4398115 baseEnd_4398115 := by
    simpa [prefixWord, tailWord_4398115, baseEnd_4398115] using wordTrace_append hprefix tailTrace_4398115
  have hstable : (prefixWord ++ tailWord_4398115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398115).length < 2 ^ (prefixWord ++ tailWord_4398115).sum := by decide
  have hdescent : baseEnd_4398115 < baseStart_4398115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398116 : List Nat := [2, 3, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_4398116 : Nat := 118140960795 + 4398116 * 2 ^ 59
def prefixEnd_4398116 : Nat := 4983230072969 + 3 ^ 40 * 4398116 * 2
def baseEnd_4398116 : Nat := 752782494076606528207813

theorem tailTrace_4398116 : CollatzResearch.WordTrace tailWord_4398116 prefixEnd_4398116 752782494076606528207813 := by
  unfold tailWord_4398116
  simp only [CollatzResearch.WordTrace]
  refine ⟨80206234467192172628363101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106941645956256230171150801 80206234467192172628363101)
  ·
    refine ⟨30077337925197064735636163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80206234467192172628363101 30077337925197064735636163)
    ·
      refine ⟨45116006887795597103454245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30077337925197064735636163 45116006887795597103454245)
      ·
        refine ⟨8459251291461674456897671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45116006887795597103454245 8459251291461674456897671)
        ·
          refine ⟨12688876937192511685346507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8459251291461674456897671 12688876937192511685346507)
          ·
            refine ⟨19033315405788767528019761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12688876937192511685346507 19033315405788767528019761)
            ·
              refine ⟨14274986554341575646014821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19033315405788767528019761 14274986554341575646014821)
              ·
                refine ⟨2676559978939045433627779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14274986554341575646014821 2676559978939045433627779)
                ·
                  refine ⟨4014839968408568150441669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676559978939045433627779 4014839968408568150441669)
                  ·
                    refine ⟨752782494076606528207813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4014839968408568150441669 752782494076606528207813)
                    ·
                      rfl

theorem cell23_4398116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_4398116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398116 prefixEnd_4398116 := by exact prefixLift 4398116
  have htrace : WordTrace (prefixWord ++ tailWord_4398116) baseStart_4398116 baseEnd_4398116 := by
    simpa [prefixWord, tailWord_4398116, baseEnd_4398116] using wordTrace_append hprefix tailTrace_4398116
  have hstable : (prefixWord ++ tailWord_4398116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398116).length < 2 ^ (prefixWord ++ tailWord_4398116).sum := by decide
  have hdescent : baseEnd_4398116 < baseStart_4398116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398150 : List Nat := [6, 1, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_4398150 : Nat := 118140960795 + 4398150 * 2 ^ 59
def prefixEnd_4398150 : Nat := 4983230072969 + 3 ^ 40 * 4398150 * 2
def baseEnd_4398150 : Nat := 752788313524024150532761

theorem tailTrace_4398150 : CollatzResearch.WordTrace tailWord_4398150 prefixEnd_4398150 752788313524024150532761 := by
  unfold tailWord_4398150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012928406758161533233247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106942472677507446042309269 5012928406758161533233247)
  ·
    refine ⟨7519392610137242299849871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5012928406758161533233247 7519392610137242299849871)
    ·
      refine ⟨11279088915205863449774807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7519392610137242299849871 11279088915205863449774807)
      ·
        refine ⟨16918633372808795174662211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11279088915205863449774807 16918633372808795174662211)
        ·
          refine ⟨25377950059213192761993317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16918633372808795174662211 25377950059213192761993317)
          ·
            refine ⟨4758365636102473642873747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25377950059213192761993317 4758365636102473642873747)
            ·
              refine ⟨7137548454153710464310621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4758365636102473642873747 7137548454153710464310621)
              ·
                refine ⟨2676580670307641424116483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7137548454153710464310621 2676580670307641424116483)
                ·
                  refine ⟨4014871005461462136174725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676580670307641424116483 4014871005461462136174725)
                  ·
                    refine ⟨752788313524024150532761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4014871005461462136174725 752788313524024150532761)
                    ·
                      rfl

theorem cell23_4398150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_4398150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398150 prefixEnd_4398150 := by exact prefixLift 4398150
  have htrace : WordTrace (prefixWord ++ tailWord_4398150) baseStart_4398150 baseEnd_4398150 := by
    simpa [prefixWord, tailWord_4398150, baseEnd_4398150] using wordTrace_append hprefix tailTrace_4398150
  have hstable : (prefixWord ++ tailWord_4398150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398150).length < 2 ^ (prefixWord ++ tailWord_4398150).sum := by decide
  have hdescent : baseEnd_4398150 < baseStart_4398150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398175 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_4398175 : Nat := 118140960795 + 4398175 * 2 ^ 59
def prefixEnd_4398175 : Nat := 4983230072969 + 3 ^ 40 * 4398175 * 2
def baseEnd_4398175 : Nat := 2258377777588434853785667

theorem tailTrace_4398175 : CollatzResearch.WordTrace tailWord_4398175 prefixEnd_4398175 2258377777588434853785667 := by
  unfold tailWord_4398175
  simp only [CollatzResearch.WordTrace]
  refine ⟨160414620841170598333123979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106943080560780398888749319 160414620841170598333123979)
  ·
    refine ⟨240621931261755897499685969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160414620841170598333123979 240621931261755897499685969)
    ·
      refine ⟨180466448446316923124764477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240621931261755897499685969 180466448446316923124764477)
      ·
        refine ⟨67674918167368846171786679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180466448446316923124764477 67674918167368846171786679)
        ·
          refine ⟨101512377251053269257680019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67674918167368846171786679 101512377251053269257680019)
          ·
            refine ⟨152268565876579903886520029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101512377251053269257680019 152268565876579903886520029)
            ·
              refine ⟨57100712203717463957445011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152268565876579903886520029 57100712203717463957445011)
              ·
                refine ⟨85651068305576195936167517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57100712203717463957445011 85651068305576195936167517)
                ·
                  refine ⟨32119150614591073476062819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85651068305576195936167517 32119150614591073476062819)
                  ·
                    refine ⟨48178725921886610214094229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32119150614591073476062819 48178725921886610214094229)
                    ·
                      refine ⟨2258377777588434853785667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48178725921886610214094229 2258377777588434853785667)
                      ·
                        rfl

theorem cell23_4398175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_4398175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398175 prefixEnd_4398175 := by exact prefixLift 4398175
  have htrace : WordTrace (prefixWord ++ tailWord_4398175) baseStart_4398175 baseEnd_4398175 := by
    simpa [prefixWord, tailWord_4398175, baseEnd_4398175] using wordTrace_append hprefix tailTrace_4398175
  have hstable : (prefixWord ++ tailWord_4398175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398175).length < 2 ^ (prefixWord ++ tailWord_4398175).sum := by decide
  have hdescent : baseEnd_4398175 < baseStart_4398175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398185 : List Nat := [1, 2, 1, 1, 1, 6, 1, 10]
def baseStart_4398185 : Nat := 118140960795 + 4398185 * 2 ^ 59
def prefixEnd_4398185 : Nat := 4983230072969 + 3 ^ 40 * 4398185 * 2
def baseEnd_4398185 : Nat := 83643811570184437580023

theorem tailTrace_4398185 : CollatzResearch.WordTrace tailWord_4398185 prefixEnd_4398185 83643811570184437580023 := by
  unfold tailWord_4398185
  simp only [CollatzResearch.WordTrace]
  refine ⟨160414985571134370040988009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106943323714089580027325339 160414985571134370040988009)
  ·
    refine ⟨120311239178350777530741007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160414985571134370040988009 120311239178350777530741007)
    ·
      refine ⟨180466858767526166296111511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120311239178350777530741007 180466858767526166296111511)
      ·
        refine ⟨270700288151289249444167267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180466858767526166296111511 270700288151289249444167267)
        ·
          refine ⟨406050432226933874166250901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270700288151289249444167267 406050432226933874166250901)
          ·
            refine ⟨19033614010637525351543011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 406050432226933874166250901 19033614010637525351543011)
            ·
              refine ⟨28550421015956288027314517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19033614010637525351543011 28550421015956288027314517)
              ·
                refine ⟨83643811570184437580023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28550421015956288027314517 83643811570184437580023)
                ·
                  rfl

theorem cell23_4398185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 10].length) (baseStart_4398185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398185 prefixEnd_4398185 := by exact prefixLift 4398185
  have htrace : WordTrace (prefixWord ++ tailWord_4398185) baseStart_4398185 baseEnd_4398185 := by
    simpa [prefixWord, tailWord_4398185, baseEnd_4398185] using wordTrace_append hprefix tailTrace_4398185
  have hstable : (prefixWord ++ tailWord_4398185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398185).length < 2 ^ (prefixWord ++ tailWord_4398185).sum := by decide
  have hdescent : baseEnd_4398185 < baseStart_4398185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398192 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_4398192 : Nat := 118140960795 + 4398192 * 2 ^ 59
def prefixEnd_4398192 : Nat := 4983230072969 + 3 ^ 40 * 4398192 * 2
def baseEnd_4398192 : Nat := 2258386506759561287273089

theorem tailTrace_4398192 : CollatzResearch.WordTrace tailWord_4398192 prefixEnd_4398192 2258386506759561287273089 := by
  unfold tailWord_4398192
  simp only [CollatzResearch.WordTrace]
  refine ⟨80207620441054505118246415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106943493921406006824328553 80207620441054505118246415)
  ·
    refine ⟨120311430661581757677369623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80207620441054505118246415 120311430661581757677369623)
    ·
      refine ⟨180467145992372636516054435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120311430661581757677369623 180467145992372636516054435)
      ·
        refine ⟨270700718988558954774081653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180467145992372636516054435 270700718988558954774081653)
        ·
          refine ⟨25378192405177402010070155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 270700718988558954774081653 25378192405177402010070155)
          ·
            refine ⟨38067288607766103015105233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25378192405177402010070155 38067288607766103015105233)
            ·
              refine ⟨28550466455824577261328925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38067288607766103015105233 28550466455824577261328925)
              ·
                refine ⟨10706424920934216472998347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28550466455824577261328925 10706424920934216472998347)
                ·
                  refine ⟨16059637381401324709497521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10706424920934216472998347 16059637381401324709497521)
                  ·
                    refine ⟨12044728036050993532123141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16059637381401324709497521 12044728036050993532123141)
                    ·
                      refine ⟨2258386506759561287273089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12044728036050993532123141 2258386506759561287273089)
                      ·
                        rfl

theorem cell23_4398192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_4398192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398192 prefixEnd_4398192 := by exact prefixLift 4398192
  have htrace : WordTrace (prefixWord ++ tailWord_4398192) baseStart_4398192 baseEnd_4398192 := by
    simpa [prefixWord, tailWord_4398192, baseEnd_4398192] using wordTrace_append hprefix tailTrace_4398192
  have hstable : (prefixWord ++ tailWord_4398192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398192).length < 2 ^ (prefixWord ++ tailWord_4398192).sum := by decide
  have hdescent : baseEnd_4398192 < baseStart_4398192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398209 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4398209 : Nat := 118140960795 + 4398209 * 2 ^ 59
def prefixEnd_4398209 : Nat := 4983230072969 + 3 ^ 40 * 4398209 * 2
def baseEnd_4398209 : Nat := 2258395235930687720760511

theorem tailTrace_4398209 : CollatzResearch.WordTrace tailWord_4398209 prefixEnd_4398209 2258395235930687720760511 := by
  unfold tailWord_4398209
  simp only [CollatzResearch.WordTrace]
  refine ⟨160415860923047422139861681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106943907282031614759907787 160415860923047422139861681)
  ·
    refine ⟨120311895692285566604896261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160415860923047422139861681 120311895692285566604896261)
    ·
      refine ⟨22558480442303543738418049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120311895692285566604896261 22558480442303543738418049)
      ·
        refine ⟨16918860331727657803813537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22558480442303543738418049 16918860331727657803813537)
        ·
          refine ⟨12689145248795743352860153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16918860331727657803813537 12689145248795743352860153)
          ·
            refine ⟨9516858936596807514645115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12689145248795743352860153 9516858936596807514645115)
            ·
              refine ⟨14275288404895211271967673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9516858936596807514645115 14275288404895211271967673)
              ·
                refine ⟨10706466303671408453975755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14275288404895211271967673 10706466303671408453975755)
                ·
                  refine ⟨16059699455507112680963633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10706466303671408453975755 16059699455507112680963633)
                  ·
                    refine ⟨12044774591630334510722725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16059699455507112680963633 12044774591630334510722725)
                    ·
                      refine ⟨2258395235930687720760511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12044774591630334510722725 2258395235930687720760511)
                      ·
                        rfl

theorem cell23_4398209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4398209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398209 prefixEnd_4398209 := by exact prefixLift 4398209
  have htrace : WordTrace (prefixWord ++ tailWord_4398209) baseStart_4398209 baseEnd_4398209 := by
    simpa [prefixWord, tailWord_4398209, baseEnd_4398209] using wordTrace_append hprefix tailTrace_4398209
  have hstable : (prefixWord ++ tailWord_4398209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398209).length < 2 ^ (prefixWord ++ tailWord_4398209).sum := by decide
  have hdescent : baseEnd_4398209 < baseStart_4398209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398216 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4398216 : Nat := 118140960795 + 4398216 * 2 ^ 59
def prefixEnd_4398216 : Nat := 4983230072969 + 3 ^ 40 * 4398216 * 2
def baseEnd_4398216 : Nat := 2258398830295269193372979

theorem tailTrace_4398216 : CollatzResearch.WordTrace tailWord_4398216 prefixEnd_4398216 2258398830295269193372979 := by
  unfold tailWord_4398216
  simp only [CollatzResearch.WordTrace]
  refine ⟨80208058117011031167683251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106944077489348041556911001 80208058117011031167683251)
  ·
    refine ⟨120312087175516546751524877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80208058117011031167683251 120312087175516546751524877)
    ·
      refine ⟨45117032690818705031821829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120312087175516546751524877 45117032690818705031821829)
      ·
        refine ⟨8459443629528507193466593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45117032690818705031821829 8459443629528507193466593)
        ·
          refine ⟨6344582722146380395099945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8459443629528507193466593 6344582722146380395099945)
          ·
            refine ⟨4758437041609785296324959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6344582722146380395099945 4758437041609785296324959)
            ·
              refine ⟨7137655562414677944487439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4758437041609785296324959 7137655562414677944487439)
              ·
                refine ⟨10706483343622016916731159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7137655562414677944487439 10706483343622016916731159)
                ·
                  refine ⟨16059725015433025375096739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10706483343622016916731159 16059725015433025375096739)
                  ·
                    refine ⟨24089587523149538062645109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16059725015433025375096739 24089587523149538062645109)
                    ·
                      refine ⟨2258398830295269193372979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24089587523149538062645109 2258398830295269193372979)
                      ·
                        rfl

theorem cell23_4398216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4398216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398216 prefixEnd_4398216 := by exact prefixLift 4398216
  have htrace : WordTrace (prefixWord ++ tailWord_4398216) baseStart_4398216 baseEnd_4398216 := by
    simpa [prefixWord, tailWord_4398216, baseEnd_4398216] using wordTrace_append hprefix tailTrace_4398216
  have hstable : (prefixWord ++ tailWord_4398216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398216).length < 2 ^ (prefixWord ++ tailWord_4398216).sum := by decide
  have hdescent : baseEnd_4398216 < baseStart_4398216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398225 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_4398225 : Nat := 118140960795 + 4398225 * 2 ^ 59
def prefixEnd_4398225 : Nat := 4983230072969 + 3 ^ 40 * 4398225 * 2
def baseEnd_4398225 : Nat := 2258403451621159658160437

theorem tailTrace_4398225 : CollatzResearch.WordTrace tailWord_4398225 prefixEnd_4398225 2258403451621159658160437 := by
  unfold tailWord_4398225
  simp only [CollatzResearch.WordTrace]
  refine ⟨160416444490989456872444129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106944296327326304581629419 160416444490989456872444129)
  ·
    refine ⟨120312333368242092654333097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160416444490989456872444129 120312333368242092654333097)
    ·
      refine ⟨90234250026181569490749823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120312333368242092654333097 90234250026181569490749823)
      ·
        refine ⟨135351375039272354236124735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90234250026181569490749823 135351375039272354236124735)
        ·
          refine ⟨203027062558908531354187103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135351375039272354236124735 203027062558908531354187103)
          ·
            refine ⟨304540593838362797031280655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203027062558908531354187103 304540593838362797031280655)
            ·
              refine ⟨456810890757544195546920983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304540593838362797031280655 456810890757544195546920983)
              ·
                refine ⟨685216336136316293320381475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456810890757544195546920983 685216336136316293320381475)
                ·
                  refine ⟨1027824504204474439980572213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685216336136316293320381475 1027824504204474439980572213)
                  ·
                    refine ⟨96358547269169478748178645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1027824504204474439980572213 96358547269169478748178645)
                    ·
                      refine ⟨2258403451621159658160437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96358547269169478748178645 2258403451621159658160437)
                      ·
                        rfl

theorem cell23_4398225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_4398225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398225 prefixEnd_4398225 := by exact prefixLift 4398225
  have htrace : WordTrace (prefixWord ++ tailWord_4398225) baseStart_4398225 baseEnd_4398225 := by
    simpa [prefixWord, tailWord_4398225, baseEnd_4398225] using wordTrace_append hprefix tailTrace_4398225
  have hstable : (prefixWord ++ tailWord_4398225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398225).length < 2 ^ (prefixWord ++ tailWord_4398225).sum := by decide
  have hdescent : baseEnd_4398225 < baseStart_4398225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398232 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 2, 7]
def baseStart_4398232 : Nat := 118140960795 + 4398232 * 2 ^ 59
def prefixEnd_4398232 : Nat := 4983230072969 + 3 ^ 40 * 4398232 * 2
def baseEnd_4398232 : Nat := 752802348661913710257635

theorem tailTrace_4398232 : CollatzResearch.WordTrace tailWord_4398232 prefixEnd_4398232 752802348661913710257635 := by
  unfold tailWord_4398232
  simp only [CollatzResearch.WordTrace]
  refine ⟨80208349900982048533974475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106944466534642731378632633 80208349900982048533974475)
  ·
    refine ⟨120312524851473072800961713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80208349900982048533974475 120312524851473072800961713)
    ·
      refine ⟨90234393638604804600721285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120312524851473072800961713 90234393638604804600721285)
      ·
        refine ⟨16918948807238400862635241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90234393638604804600721285 16918948807238400862635241)
        ·
          refine ⟨12689211605428800646976431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16918948807238400862635241 12689211605428800646976431)
          ·
            refine ⟨19033817408143200970464647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12689211605428800646976431 19033817408143200970464647)
            ·
              refine ⟨28550726112214801455696971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19033817408143200970464647 28550726112214801455696971)
              ·
                refine ⟨42826089168322202183545457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28550726112214801455696971 42826089168322202183545457)
                ·
                  refine ⟨32119566876241651637659093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42826089168322202183545457 32119566876241651637659093)
                  ·
                    refine ⟨752802348661913710257635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32119566876241651637659093 752802348661913710257635)
                    ·
                      rfl

theorem cell23_4398232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_4398232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398232 prefixEnd_4398232 := by exact prefixLift 4398232
  have htrace : WordTrace (prefixWord ++ tailWord_4398232) baseStart_4398232 baseEnd_4398232 := by
    simpa [prefixWord, tailWord_4398232, baseEnd_4398232] using wordTrace_append hprefix tailTrace_4398232
  have hstable : (prefixWord ++ tailWord_4398232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398232).length < 2 ^ (prefixWord ++ tailWord_4398232).sum := by decide
  have hdescent : baseEnd_4398232 < baseStart_4398232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398339 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 2, 5]
def baseStart_4398339 : Nat := 118140960795 + 4398339 * 2 ^ 59
def prefixEnd_4398339 : Nat := 4983230072969 + 3 ^ 40 * 4398339 * 2
def baseEnd_4398339 : Nat := 752820662805257404044971

theorem tailTrace_4398339 : CollatzResearch.WordTrace tailWord_4398339 prefixEnd_4398339 752820662805257404044971 := by
  unfold tailWord_4398339
  simp only [CollatzResearch.WordTrace]
  refine ⟨160420602412576454342094071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106947068275050969561396047 160420602412576454342094071)
  ·
    refine ⟨240630903618864681513141107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160420602412576454342094071 240630903618864681513141107)
    ·
      refine ⟨360946355428297022269711661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240630903618864681513141107 360946355428297022269711661)
      ·
        refine ⟨135354883285611383351141873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360946355428297022269711661 135354883285611383351141873)
        ·
          refine ⟨101516162464208537513356405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135354883285611383351141873 101516162464208537513356405)
          ·
            refine ⟨9517140231019550391877163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101516162464208537513356405 9517140231019550391877163)
            ·
              refine ⟨14275710346529325587815745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9517140231019550391877163 14275710346529325587815745)
              ·
                refine ⟨10706782759896994190861809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14275710346529325587815745 10706782759896994190861809)
                ·
                  refine ⟨8030087069922745643146357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10706782759896994190861809 8030087069922745643146357)
                  ·
                    refine ⟨752820662805257404044971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8030087069922745643146357 752820662805257404044971)
                    ·
                      rfl

theorem cell23_4398339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 5].length) (baseStart_4398339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398339 prefixEnd_4398339 := by exact prefixLift 4398339
  have htrace : WordTrace (prefixWord ++ tailWord_4398339) baseStart_4398339 baseEnd_4398339 := by
    simpa [prefixWord, tailWord_4398339, baseEnd_4398339] using wordTrace_append hprefix tailTrace_4398339
  have hstable : (prefixWord ++ tailWord_4398339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398339).length < 2 ^ (prefixWord ++ tailWord_4398339).sum := by decide
  have hdescent : baseEnd_4398339 < baseStart_4398339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398359 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4398359 : Nat := 118140960795 + 4398359 * 2 ^ 59
def prefixEnd_4398359 : Nat := 4983230072969 + 3 ^ 40 * 4398359 * 2
def baseEnd_4398359 : Nat := 2258472258028862133884821

theorem tailTrace_4398359 : CollatzResearch.WordTrace tailWord_4398359 prefixEnd_4398359 2258472258028862133884821 := by
  unfold tailWord_4398359
  simp only [CollatzResearch.WordTrace]
  refine ⟨160421331872503997757822131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106947554581669331838548087 160421331872503997757822131)
  ·
    refine ⟨240631997808755996636733197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160421331872503997757822131 240631997808755996636733197)
    ·
      refine ⟨90236999178283498738774949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240631997808755996636733197 90236999178283498738774949)
      ·
        refine ⟨16919437345928156013520303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90236999178283498738774949 16919437345928156013520303)
        ·
          refine ⟨25379156018892234020280455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16919437345928156013520303 25379156018892234020280455)
          ·
            refine ⟨38068734028338351030420683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25379156018892234020280455 38068734028338351030420683)
            ·
              refine ⟨57103101042507526545631025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38068734028338351030420683 57103101042507526545631025)
              ·
                refine ⟨42827325781880644909223269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57103101042507526545631025 42827325781880644909223269)
                ·
                  refine ⟨8030123584102620920479363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42827325781880644909223269 8030123584102620920479363)
                  ·
                    refine ⟨12045185376153931380719045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8030123584102620920479363 12045185376153931380719045)
                    ·
                      refine ⟨2258472258028862133884821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12045185376153931380719045 2258472258028862133884821)
                      ·
                        rfl

theorem cell23_4398359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4398359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398359 prefixEnd_4398359 := by exact prefixLift 4398359
  have htrace : WordTrace (prefixWord ++ tailWord_4398359) baseStart_4398359 baseEnd_4398359 := by
    simpa [prefixWord, tailWord_4398359, baseEnd_4398359] using wordTrace_append hprefix tailTrace_4398359
  have hstable : (prefixWord ++ tailWord_4398359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398359).length < 2 ^ (prefixWord ++ tailWord_4398359).sum := by decide
  have hdescent : baseEnd_4398359 < baseStart_4398359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398369 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 5, 4]
def baseStart_4398369 : Nat := 118140960795 + 4398369 * 2 ^ 59
def prefixEnd_4398369 : Nat := 4983230072969 + 3 ^ 40 * 4398369 * 2
def baseEnd_4398369 : Nat := 752825797611802364919925

theorem tailTrace_4398369 : CollatzResearch.WordTrace tailWord_4398369 prefixEnd_4398369 752825797611802364919925 := by
  unfold tailWord_4398369
  simp only [CollatzResearch.WordTrace]
  refine ⟨160421696602467769465686161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106947797734978512977124107 160421696602467769465686161)
  ·
    refine ⟨120316272451850827099264621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160421696602467769465686161 120316272451850827099264621)
    ·
      refine ⟨45118602169444060162224233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120316272451850827099264621 45118602169444060162224233)
      ·
        refine ⟨33838951627083045121668175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45118602169444060162224233 33838951627083045121668175)
        ·
          refine ⟨50758427440624567682502263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33838951627083045121668175 50758427440624567682502263)
          ·
            refine ⟨76137641160936851523753395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50758427440624567682502263 76137641160936851523753395)
            ·
              refine ⟨114206461741405277285630093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76137641160936851523753395 114206461741405277285630093)
              ·
                refine ⟨42827423153026978982111285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114206461741405277285630093 42827423153026978982111285)
                ·
                  refine ⟨4015070920596279279572933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42827423153026978982111285 4015070920596279279572933)
                  ·
                    refine ⟨752825797611802364919925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015070920596279279572933 752825797611802364919925)
                    ·
                      rfl

theorem cell23_4398369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_4398369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398369 prefixEnd_4398369 := by exact prefixLift 4398369
  have htrace : WordTrace (prefixWord ++ tailWord_4398369) baseStart_4398369 baseEnd_4398369 := by
    simpa [prefixWord, tailWord_4398369, baseEnd_4398369] using wordTrace_append hprefix tailTrace_4398369
  have hstable : (prefixWord ++ tailWord_4398369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398369).length < 2 ^ (prefixWord ++ tailWord_4398369).sum := by decide
  have hdescent : baseEnd_4398369 < baseStart_4398369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398376 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4398376 : Nat := 118140960795 + 4398376 * 2 ^ 59
def prefixEnd_4398376 : Nat := 4983230072969 + 3 ^ 40 * 4398376 * 2
def baseEnd_4398376 : Nat := 2258480987199988567372243

theorem tailTrace_4398376 : CollatzResearch.WordTrace tailWord_4398376 prefixEnd_4398376 2258480987199988567372243 := by
  unfold tailWord_4398376
  simp only [CollatzResearch.WordTrace]
  refine ⟨80210975956721204830595491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106947967942294939774127321 80210975956721204830595491)
  ·
    refine ⟨120316463935081807245893237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80210975956721204830595491 120316463935081807245893237)
    ·
      refine ⟨11279668493913919429302491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120316463935081807245893237 11279668493913919429302491)
      ·
        refine ⟨16919502740870879143953737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11279668493913919429302491 16919502740870879143953737)
        ·
          refine ⟨12689627055653159357965303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16919502740870879143953737 12689627055653159357965303)
          ·
            refine ⟨19034440583479739036947955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12689627055653159357965303 19034440583479739036947955)
            ·
              refine ⟨28551660875219608555421933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19034440583479739036947955 28551660875219608555421933)
              ·
                refine ⟨10706872828207353208283225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28551660875219608555421933 10706872828207353208283225)
                ·
                  refine ⟨8030154621155514906212419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10706872828207353208283225 8030154621155514906212419)
                  ·
                    refine ⟨12045231931733272359318629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8030154621155514906212419 12045231931733272359318629)
                    ·
                      refine ⟨2258480987199988567372243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12045231931733272359318629 2258480987199988567372243)
                      ·
                        rfl

theorem cell23_4398376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4398376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398376 prefixEnd_4398376 := by exact prefixLift 4398376
  have htrace : WordTrace (prefixWord ++ tailWord_4398376) baseStart_4398376 baseEnd_4398376 := by
    simpa [prefixWord, tailWord_4398376, baseEnd_4398376] using wordTrace_append hprefix tailTrace_4398376
  have hstable : (prefixWord ++ tailWord_4398376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398376).length < 2 ^ (prefixWord ++ tailWord_4398376).sum := by decide
  have hdescent : baseEnd_4398376 < baseStart_4398376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398396 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_4398396 : Nat := 118140960795 + 4398396 * 2 ^ 59
def prefixEnd_4398396 : Nat := 4983230072969 + 3 ^ 40 * 4398396 * 2
def baseEnd_4398396 : Nat := 2258491256813078489122151

theorem tailTrace_4398396 : CollatzResearch.WordTrace tailWord_4398396 prefixEnd_4398396 2258491256813078489122151 := by
  unfold tailWord_4398396
  simp only [CollatzResearch.WordTrace]
  refine ⟨80211340686684976538459521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106948454248913302051279361 80211340686684976538459521)
  ·
    refine ⟨60158505515013732403844641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80211340686684976538459521 60158505515013732403844641)
    ·
      refine ⟨45118879136260299302883481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60158505515013732403844641 45118879136260299302883481)
      ·
        refine ⟨33839159352195224477162611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45118879136260299302883481 33839159352195224477162611)
        ·
          refine ⟨50758739028292836715743917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33839159352195224477162611 50758739028292836715743917)
          ·
            refine ⟨19034527135609813768403969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50758739028292836715743917 19034527135609813768403969)
            ·
              refine ⟨14275895351707360326302977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19034527135609813768403969 14275895351707360326302977)
              ·
                refine ⟨10706921513780520244727233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14275895351707360326302977 10706921513780520244727233)
                ·
                  refine ⟨8030191135335390183545425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10706921513780520244727233 8030191135335390183545425)
                  ·
                    refine ⟨6022643351501542637659069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8030191135335390183545425 6022643351501542637659069)
                    ·
                      refine ⟨2258491256813078489122151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6022643351501542637659069 2258491256813078489122151)
                      ·
                        rfl

theorem cell23_4398396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_4398396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398396 prefixEnd_4398396 := by exact prefixLift 4398396
  have htrace : WordTrace (prefixWord ++ tailWord_4398396) baseStart_4398396 baseEnd_4398396 := by
    simpa [prefixWord, tailWord_4398396, baseEnd_4398396] using wordTrace_append hprefix tailTrace_4398396
  have hstable : (prefixWord ++ tailWord_4398396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398396).length < 2 ^ (prefixWord ++ tailWord_4398396).sum := by decide
  have hdescent : baseEnd_4398396 < baseStart_4398396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398399 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 6]
def baseStart_4398399 : Nat := 118140960795 + 4398399 * 2 ^ 59
def prefixEnd_4398399 : Nat := 4983230072969 + 3 ^ 40 * 4398399 * 2
def baseEnd_4398399 : Nat := 250943644139449108598293

theorem tailTrace_4398399 : CollatzResearch.WordTrace tailWord_4398399 prefixEnd_4398399 250943644139449108598293 := by
  unfold tailWord_4398399
  simp only [CollatzResearch.WordTrace]
  refine ⟨160422790792359084589278251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106948527194906056392852167 160422790792359084589278251)
  ·
    refine ⟨240634186188538626883917377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160422790792359084589278251 240634186188538626883917377)
    ·
      refine ⟨180475639641403970162938033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240634186188538626883917377 180475639641403970162938033)
      ·
        refine ⟨135356729731052977622203525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180475639641403970162938033 135356729731052977622203525)
        ·
          refine ⟨25379386824572433304163161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135356729731052977622203525 25379386824572433304163161)
          ·
            refine ⟨19034540118429324978122371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25379386824572433304163161 19034540118429324978122371)
            ·
              refine ⟨28551810177643987467183557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19034540118429324978122371 28551810177643987467183557)
              ·
                refine ⟨5353464408308247650096917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28551810177643987467183557 5353464408308247650096917)
                ·
                  refine ⟨250943644139449108598293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5353464408308247650096917 250943644139449108598293)
                  ·
                    rfl

theorem cell23_4398399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 6].length) (baseStart_4398399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398399 prefixEnd_4398399 := by exact prefixLift 4398399
  have htrace : WordTrace (prefixWord ++ tailWord_4398399) baseStart_4398399 baseEnd_4398399 := by
    simpa [prefixWord, tailWord_4398399, baseEnd_4398399] using wordTrace_append hprefix tailTrace_4398399
  have hstable : (prefixWord ++ tailWord_4398399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398399).length < 2 ^ (prefixWord ++ tailWord_4398399).sum := by decide
  have hdescent : baseEnd_4398399 < baseStart_4398399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398426 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_4398426 : Nat := 118140960795 + 4398426 * 2 ^ 59
def prefixEnd_4398426 : Nat := 4983230072969 + 3 ^ 40 * 4398426 * 2
def baseEnd_4398426 : Nat := 2258506661232713371747013

theorem tailTrace_4398426 : CollatzResearch.WordTrace tailWord_4398426 prefixEnd_4398426 2258506661232713371747013 := by
  unfold tailWord_4398426
  simp only [CollatzResearch.WordTrace]
  refine ⟨40105943890815317050127783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106949183708840845467007421 40105943890815317050127783)
  ·
    refine ⟨60158915836222975575191675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40105943890815317050127783 60158915836222975575191675)
    ·
      refine ⟨90238373754334463362787513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60158915836222975575191675 90238373754334463362787513)
      ·
        refine ⟨67678780315750847522090635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90238373754334463362787513 67678780315750847522090635)
        ·
          refine ⟨101518170473626271283135953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67678780315750847522090635 101518170473626271283135953)
          ·
            refine ⟨76138627855219703462351965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101518170473626271283135953 76138627855219703462351965)
            ·
              refine ⟨28551985445707388798381987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76138627855219703462351965 28551985445707388798381987)
              ·
                refine ⟨42827978168561083197572981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28551985445707388798381987 42827978168561083197572981)
                ·
                  refine ⟨4015122953302601549772467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42827978168561083197572981 4015122953302601549772467)
                  ·
                    refine ⟨6022684429953902324658701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4015122953302601549772467 6022684429953902324658701)
                    ·
                      refine ⟨2258506661232713371747013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6022684429953902324658701 2258506661232713371747013)
                      ·
                        rfl

theorem cell23_4398426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_4398426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398426 prefixEnd_4398426 := by exact prefixLift 4398426
  have htrace : WordTrace (prefixWord ++ tailWord_4398426) baseStart_4398426 baseEnd_4398426 := by
    simpa [prefixWord, tailWord_4398426, baseEnd_4398426] using wordTrace_append hprefix tailTrace_4398426
  have hstable : (prefixWord ++ tailWord_4398426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398426).length < 2 ^ (prefixWord ++ tailWord_4398426).sum := by decide
  have hdescent : baseEnd_4398426 < baseStart_4398426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398469 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_4398469 : Nat := 118140960795 + 4398469 * 2 ^ 59
def prefixEnd_4398469 : Nat := 4983230072969 + 3 ^ 40 * 4398469 * 2
def baseEnd_4398469 : Nat := 2258528740900856703509315

theorem tailTrace_4398469 : CollatzResearch.WordTrace tailWord_4398469 prefixEnd_4398469 2258528740900856703509315 := by
  unfold tailWord_4398469
  simp only [CollatzResearch.WordTrace]
  refine ⟨160425343902105486544326461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106950229268070324362884307 160425343902105486544326461)
  ·
    refine ⟨60159503963289557454122423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160425343902105486544326461 60159503963289557454122423)
    ·
      refine ⟨90239255944934336181183635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60159503963289557454122423 90239255944934336181183635)
      ·
        refine ⟨135358883917401504271775453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90239255944934336181183635 135358883917401504271775453)
        ·
          refine ⟨50759581469025564101915795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135358883917401504271775453 50759581469025564101915795)
          ·
            refine ⟨76139372203538346152873693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50759581469025564101915795 76139372203538346152873693)
            ·
              refine ⟨28552264576326879807327635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76139372203538346152873693 28552264576326879807327635)
              ·
                refine ⟨42828396864490319710991453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28552264576326879807327635 42828396864490319710991453)
                ·
                  refine ⟨16060648824183869891621795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42828396864490319710991453 16060648824183869891621795)
                  ·
                    refine ⟨24090973236275804837432693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16060648824183869891621795 24090973236275804837432693)
                    ·
                      refine ⟨2258528740900856703509315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24090973236275804837432693 2258528740900856703509315)
                      ·
                        rfl

theorem cell23_4398469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_4398469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398469 prefixEnd_4398469 := by exact prefixLift 4398469
  have htrace : WordTrace (prefixWord ++ tailWord_4398469) baseStart_4398469 baseEnd_4398469 := by
    simpa [prefixWord, tailWord_4398469, baseEnd_4398469] using wordTrace_append hprefix tailTrace_4398469
  have hstable : (prefixWord ++ tailWord_4398469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398469).length < 2 ^ (prefixWord ++ tailWord_4398469).sum := by decide
  have hdescent : baseEnd_4398469 < baseStart_4398469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398489 : List Nat := [1, 2, 1, 2, 1, 6, 1, 9]
def baseStart_4398489 : Nat := 118140960795 + 4398489 * 2 ^ 59
def prefixEnd_4398489 : Nat := 4983230072969 + 3 ^ 40 * 4398489 * 2
def baseEnd_4398489 : Nat := 83649592981998023157749

theorem tailTrace_4398489 : CollatzResearch.WordTrace tailWord_4398489 prefixEnd_4398489 83649592981998023157749 := by
  unfold tailWord_4398489
  simp only [CollatzResearch.WordTrace]
  refine ⟨160426073362033029960054521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106950715574688686640036347 160426073362033029960054521)
  ·
    refine ⟨120319555021524772470040891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160426073362033029960054521 120319555021524772470040891)
    ·
      refine ⟨180479332532287158705061337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120319555021524772470040891 180479332532287158705061337)
      ·
        refine ⟨135359499399215369028796003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180479332532287158705061337 135359499399215369028796003)
        ·
          refine ⟨203039249098823053543194005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135359499399215369028796003 203039249098823053543194005)
          ·
            refine ⟨9517464801507330634837219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203039249098823053543194005 9517464801507330634837219)
            ·
              refine ⟨14276197202260995952255829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9517464801507330634837219 14276197202260995952255829)
              ·
                refine ⟨83649592981998023157749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14276197202260995952255829 83649592981998023157749)
                ·
                  rfl

theorem cell23_4398489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 9].length) (baseStart_4398489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398489 prefixEnd_4398489 := by exact prefixLift 4398489
  have htrace : WordTrace (prefixWord ++ tailWord_4398489) baseStart_4398489 baseEnd_4398489 := by
    simpa [prefixWord, tailWord_4398489, baseEnd_4398489] using wordTrace_append hprefix tailTrace_4398489
  have hstable : (prefixWord ++ tailWord_4398489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398489).length < 2 ^ (prefixWord ++ tailWord_4398489).sum := by decide
  have hdescent : baseEnd_4398489 < baseStart_4398489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398503 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_4398503 : Nat := 118140960795 + 4398503 * 2 ^ 59
def prefixEnd_4398503 : Nat := 4983230072969 + 3 ^ 40 * 4398503 * 2
def baseEnd_4398503 : Nat := 2258546199243109570484159

theorem tailTrace_4398503 : CollatzResearch.WordTrace tailWord_4398503 prefixEnd_4398503 2258546199243109570484159 := by
  unfold tailWord_4398503
  simp only [CollatzResearch.WordTrace]
  refine ⟨160426583983982310351064163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106951055989321540234042775 160426583983982310351064163)
  ·
    refine ⟨240639875975973465526596245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160426583983982310351064163 240639875975973465526596245)
    ·
      refine ⟨11279994186373756196559199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 240639875975973465526596245 11279994186373756196559199)
      ·
        refine ⟨16919991279560634294838799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11279994186373756196559199 16919991279560634294838799)
        ·
          refine ⟨25379986919340951442258199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16919991279560634294838799 25379986919340951442258199)
          ·
            refine ⟨38069980379011427163387299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25379986919340951442258199 38069980379011427163387299)
            ·
              refine ⟨57104970568517140745080949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38069980379011427163387299 57104970568517140745080949)
              ·
                refine ⟨5353590990798481944851339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57104970568517140745080949 5353590990798481944851339)
                ·
                  refine ⟨8030386486197722917277009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5353590990798481944851339 8030386486197722917277009)
                  ·
                    refine ⟨6022789864648292187957757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8030386486197722917277009 6022789864648292187957757)
                    ·
                      refine ⟨2258546199243109570484159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6022789864648292187957757 2258546199243109570484159)
                      ·
                        rfl

theorem cell23_4398503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_4398503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398503 prefixEnd_4398503 := by exact prefixLift 4398503
  have htrace : WordTrace (prefixWord ++ tailWord_4398503) baseStart_4398503 baseEnd_4398503 := by
    simpa [prefixWord, tailWord_4398503, baseEnd_4398503] using wordTrace_append hprefix tailTrace_4398503
  have hstable : (prefixWord ++ tailWord_4398503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398503).length < 2 ^ (prefixWord ++ tailWord_4398503).sum := by decide
  have hdescent : baseEnd_4398503 < baseStart_4398503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398517 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_4398517 : Nat := 118140960795 + 4398517 * 2 ^ 59
def prefixEnd_4398517 : Nat := 4983230072969 + 3 ^ 40 * 4398517 * 2
def baseEnd_4398517 : Nat := 2258553387972272515709095

theorem tailTrace_4398517 : CollatzResearch.WordTrace tailWord_4398517 prefixEnd_4398517 2258553387972272515709095 := by
  unfold tailWord_4398517
  simp only [CollatzResearch.WordTrace]
  refine ⟨160427094605931590742073805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106951396403954393828049203 160427094605931590742073805)
  ·
    refine ⟨60160160477224346528277677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160427094605931590742073805 60160160477224346528277677)
    ·
      refine ⟨22560060178959129948104129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60160160477224346528277677 22560060178959129948104129)
      ·
        refine ⟨16920045134219347461078097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22560060178959129948104129 16920045134219347461078097)
        ·
          refine ⟨12690033850664510595808573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16920045134219347461078097 12690033850664510595808573)
          ·
            refine ⟨4758762693999191473428215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12690033850664510595808573 4758762693999191473428215)
            ·
              refine ⟨7138144040998787210142323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4758762693999191473428215 7138144040998787210142323)
              ·
                refine ⟨10707216061498180815213485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7138144040998787210142323 10707216061498180815213485)
                ·
                  refine ⟨4015206023061817805705057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10707216061498180815213485 4015206023061817805705057)
                  ·
                    refine ⟨3011404517296363354278793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4015206023061817805705057 3011404517296363354278793)
                    ·
                      refine ⟨2258553387972272515709095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011404517296363354278793 2258553387972272515709095)
                      ·
                        rfl

theorem cell23_4398517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_4398517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398517 prefixEnd_4398517 := by exact prefixLift 4398517
  have htrace : WordTrace (prefixWord ++ tailWord_4398517) baseStart_4398517 baseEnd_4398517 := by
    simpa [prefixWord, tailWord_4398517, baseEnd_4398517] using wordTrace_append hprefix tailTrace_4398517
  have hstable : (prefixWord ++ tailWord_4398517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398517).length < 2 ^ (prefixWord ++ tailWord_4398517).sum := by decide
  have hdescent : baseEnd_4398517 < baseStart_4398517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398519 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 2, 7]
def baseStart_4398519 : Nat := 118140960795 + 4398519 * 2 ^ 59
def prefixEnd_4398519 : Nat := 4983230072969 + 3 ^ 40 * 4398519 * 2
def baseEnd_4398519 : Nat := 752851471644527169294695

theorem tailTrace_4398519 : CollatzResearch.WordTrace tailWord_4398519 prefixEnd_4398519 752851471644527169294695 := by
  unfold tailWord_4398519
  simp only [CollatzResearch.WordTrace]
  refine ⟨160427167551924345083646611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106951445034616230055764407 160427167551924345083646611)
  ·
    refine ⟨240640751327886517625469917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160427167551924345083646611 240640751327886517625469917)
    ·
      refine ⟨90240281747957444109551219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240640751327886517625469917 90240281747957444109551219)
      ·
        refine ⟨135360422621936166164326829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90240281747957444109551219 135360422621936166164326829)
        ·
          refine ⟨50760158483226062311622561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135360422621936166164326829 50760158483226062311622561)
          ·
            refine ⟨38070118862419546733716921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50760158483226062311622561 38070118862419546733716921)
            ·
              refine ⟨28552589146814660050287691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38070118862419546733716921 28552589146814660050287691)
              ·
                refine ⟨42828883720221990075431537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28552589146814660050287691 42828883720221990075431537)
                ·
                  refine ⟨32121662790166492556573653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42828883720221990075431537 32121662790166492556573653)
                  ·
                    refine ⟨752851471644527169294695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32121662790166492556573653 752851471644527169294695)
                    ·
                      rfl

theorem cell23_4398519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_4398519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398519 prefixEnd_4398519 := by exact prefixLift 4398519
  have htrace : WordTrace (prefixWord ++ tailWord_4398519) baseStart_4398519 baseEnd_4398519 := by
    simpa [prefixWord, tailWord_4398519, baseEnd_4398519] using wordTrace_append hprefix tailTrace_4398519
  have hstable : (prefixWord ++ tailWord_4398519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398519).length < 2 ^ (prefixWord ++ tailWord_4398519).sum := by decide
  have hdescent : baseEnd_4398519 < baseStart_4398519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398550 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4398550 : Nat := 118140960795 + 4398550 * 2 ^ 59
def prefixEnd_4398550 : Nat := 4983230072969 + 3 ^ 40 * 4398550 * 2
def baseEnd_4398550 : Nat := 2258570332833870886596443

theorem tailTrace_4398550 : CollatzResearch.WordTrace tailWord_4398550 prefixEnd_4398550 2258570332833870886596443 := by
  unfold tailWord_4398550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10026768638425752336126569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106952198809874691585350069 10026768638425752336126569)
  ·
    refine ⟨7520076478819314252094927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10026768638425752336126569 7520076478819314252094927)
    ·
      refine ⟨11280114718228971378142391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520076478819314252094927 11280114718228971378142391)
      ·
        refine ⟨16920172077343457067213587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11280114718228971378142391 16920172077343457067213587)
        ·
          refine ⟨25380258116015185600820381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16920172077343457067213587 25380258116015185600820381)
          ·
            refine ⟨9517596793505694600307643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25380258116015185600820381 9517596793505694600307643)
            ·
              refine ⟨14276395190258541900461465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9517596793505694600307643 14276395190258541900461465)
              ·
                refine ⟨10707296392693906425346099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14276395190258541900461465 10707296392693906425346099)
                ·
                  refine ⟨16060944589040859638019149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10707296392693906425346099 16060944589040859638019149)
                  ·
                    refine ⟨6022854220890322364257181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16060944589040859638019149 6022854220890322364257181)
                    ·
                      refine ⟨2258570332833870886596443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6022854220890322364257181 2258570332833870886596443)
                      ·
                        rfl

theorem cell23_4398550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4398550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398550 prefixEnd_4398550 := by exact prefixLift 4398550
  have htrace : WordTrace (prefixWord ++ tailWord_4398550) baseStart_4398550 baseEnd_4398550 := by
    simpa [prefixWord, tailWord_4398550, baseEnd_4398550] using wordTrace_append hprefix tailTrace_4398550
  have hstable : (prefixWord ++ tailWord_4398550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398550).length < 2 ^ (prefixWord ++ tailWord_4398550).sum := by decide
  have hdescent : baseEnd_4398550 < baseStart_4398550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398576 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3]
def baseStart_4398576 : Nat := 118140960795 + 4398576 * 2 ^ 59
def prefixEnd_4398576 : Nat := 4983230072969 + 3 ^ 40 * 4398576 * 2
def baseEnd_4398576 : Nat := 2258583683330887784871323

theorem tailTrace_4398576 : CollatzResearch.WordTrace tailWord_4398576 prefixEnd_4398576 2258583683330887784871323 := by
  unfold tailWord_4398576
  simp only [CollatzResearch.WordTrace]
  refine ⟨80214623256358921909235791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106952831008478562545647721 80214623256358921909235791)
  ·
    refine ⟨120321934884538382863853687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80214623256358921909235791 120321934884538382863853687)
    ·
      refine ⟨180482902326807574295780531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120321934884538382863853687 180482902326807574295780531)
      ·
        refine ⟨270724353490211361443670797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180482902326807574295780531 270724353490211361443670797)
        ·
          refine ⟨101521632558829260541376549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270724353490211361443670797 101521632558829260541376549)
          ·
            refine ⟨19035306104780486351508103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101521632558829260541376549 19035306104780486351508103)
            ·
              refine ⟨28552959157170729527262155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19035306104780486351508103 28552959157170729527262155)
              ·
                refine ⟨42829438735756094290893233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28552959157170729527262155 42829438735756094290893233)
                ·
                  refine ⟨32122079051817070718169925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42829438735756094290893233 32122079051817070718169925)
                  ·
                    refine ⟨6022889822215700759656861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32122079051817070718169925 6022889822215700759656861)
                    ·
                      refine ⟨2258583683330887784871323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6022889822215700759656861 2258583683330887784871323)
                      ·
                        rfl

theorem cell23_4398576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_4398576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398576 prefixEnd_4398576 := by exact prefixLift 4398576
  have htrace : WordTrace (prefixWord ++ tailWord_4398576) baseStart_4398576 baseEnd_4398576 := by
    simpa [prefixWord, tailWord_4398576, baseEnd_4398576] using wordTrace_append hprefix tailTrace_4398576
  have hstable : (prefixWord ++ tailWord_4398576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398576).length < 2 ^ (prefixWord ++ tailWord_4398576).sum := by decide
  have hdescent : baseEnd_4398576 < baseStart_4398576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398586 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_4398586 : Nat := 118140960795 + 4398586 * 2 ^ 59
def prefixEnd_4398586 : Nat := 4983230072969 + 3 ^ 40 * 4398586 * 2
def baseEnd_4398586 : Nat := 2258588818137432745746277

theorem tailTrace_4398586 : CollatzResearch.WordTrace tailWord_4398586 prefixEnd_4398586 2258588818137432745746277 := by
  unfold tailWord_4398586
  simp only [CollatzResearch.WordTrace]
  refine ⟨40107402810670403881583903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106953074161787743684223741 40107402810670403881583903)
  ·
    refine ⟨60161104216005605822375855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40107402810670403881583903 60161104216005605822375855)
    ·
      refine ⟨90241656324008408733563783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60161104216005605822375855 90241656324008408733563783)
      ·
        refine ⟨135362484486012613100345675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90241656324008408733563783 135362484486012613100345675)
        ·
          refine ⟨203043726729018919650518513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135362484486012613100345675 203043726729018919650518513)
          ·
            refine ⟨152282795046764189737888885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203043726729018919650518513 152282795046764189737888885)
            ·
              refine ⟨14276512035634142787927083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152282795046764189737888885 14276512035634142787927083)
              ·
                refine ⟨21414768053451214181890625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14276512035634142787927083 21414768053451214181890625)
                ·
                  refine ⟨16061076040088410636417969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21414768053451214181890625 16061076040088410636417969)
                  ·
                    refine ⟨12045807030066307977313477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16061076040088410636417969 12045807030066307977313477)
                    ·
                      refine ⟨2258588818137432745746277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12045807030066307977313477 2258588818137432745746277)
                      ·
                        rfl

theorem cell23_4398586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_4398586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398586 prefixEnd_4398586 := by exact prefixLift 4398586
  have htrace : WordTrace (prefixWord ++ tailWord_4398586) baseStart_4398586 baseEnd_4398586 := by
    simpa [prefixWord, tailWord_4398586, baseEnd_4398586] using wordTrace_append hprefix tailTrace_4398586
  have hstable : (prefixWord ++ tailWord_4398586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398586).length < 2 ^ (prefixWord ++ tailWord_4398586).sum := by decide
  have hdescent : baseEnd_4398586 < baseStart_4398586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398613 : List Nat := [1, 3, 2, 1, 3, 2, 1, 5, 5]
def baseStart_4398613 : Nat := 118140960795 + 4398613 * 2 ^ 59
def prefixEnd_4398613 : Nat := 4983230072969 + 3 ^ 40 * 4398613 * 2
def baseEnd_4398613 : Nat := 250955853568344904456517

theorem tailTrace_4398613 : CollatzResearch.WordTrace tailWord_4398613 prefixEnd_4398613 250955853568344904456517 := by
  unfold tailWord_4398613
  simp only [CollatzResearch.WordTrace]
  refine ⟨160430596013583799137568493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106953730675722532758378995 160430596013583799137568493)
  ·
    refine ⟨60161473505093924676588185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160430596013583799137568493 60161473505093924676588185)
    ·
      refine ⟨45121105128820443507441139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60161473505093924676588185 45121105128820443507441139)
      ·
        refine ⟨67681657693230665261161709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45121105128820443507441139 67681657693230665261161709)
        ·
          refine ⟨25380621634961499472935641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67681657693230665261161709 25380621634961499472935641)
          ·
            refine ⟨19035466226221124604701731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25380621634961499472935641 19035466226221124604701731)
            ·
              refine ⟨28553199339331686907052597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19035466226221124604701731 28553199339331686907052597)
              ·
                refine ⟨2676862438062345647536181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28553199339331686907052597 2676862438062345647536181)
                ·
                  refine ⟨250955853568344904456517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2676862438062345647536181 250955853568344904456517)
                  ·
                    rfl

theorem cell23_4398613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_4398613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398613 prefixEnd_4398613 := by exact prefixLift 4398613
  have htrace : WordTrace (prefixWord ++ tailWord_4398613) baseStart_4398613 baseEnd_4398613 := by
    simpa [prefixWord, tailWord_4398613, baseEnd_4398613] using wordTrace_append hprefix tailTrace_4398613
  have hstable : (prefixWord ++ tailWord_4398613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398613).length < 2 ^ (prefixWord ++ tailWord_4398613).sum := by decide
  have hdescent : baseEnd_4398613 < baseStart_4398613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398624 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4398624 : Nat := 118140960795 + 4398624 * 2 ^ 59
def prefixEnd_4398624 : Nat := 4983230072969 + 3 ^ 40 * 4398624 * 2
def baseEnd_4398624 : Nat := 2258608330402303597071103

theorem tailTrace_4398624 : CollatzResearch.WordTrace tailWord_4398624 prefixEnd_4398624 2258608330402303597071103 := by
  unfold tailWord_4398624
  simp only [CollatzResearch.WordTrace]
  refine ⟨80215498608271974008109463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106953998144362632010812617 80215498608271974008109463)
  ·
    refine ⟨120323247912407961012164195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80215498608271974008109463 120323247912407961012164195)
    ·
      refine ⟨180484871868611941518246293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120323247912407961012164195 180484871868611941518246293)
      ·
        refine ⟨8460228368841184758667795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180484871868611941518246293 8460228368841184758667795)
        ·
          refine ⟨12690342553261777138001693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8460228368841184758667795 12690342553261777138001693)
          ·
            refine ⟨4758878457473166426750635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12690342553261777138001693 4758878457473166426750635)
            ·
              refine ⟨7138317686209749640125953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4758878457473166426750635 7138317686209749640125953)
              ·
                refine ⟨5353738264657312230094465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7138317686209749640125953 5353738264657312230094465)
                ·
                  refine ⟨4015303698492984172570849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5353738264657312230094465 4015303698492984172570849)
                  ·
                    refine ⟨3011477773869738129428137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4015303698492984172570849 3011477773869738129428137)
                    ·
                      refine ⟨2258608330402303597071103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011477773869738129428137 2258608330402303597071103)
                      ·
                        rfl

theorem cell23_4398624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4398624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398624 prefixEnd_4398624 := by exact prefixLift 4398624
  have htrace : WordTrace (prefixWord ++ tailWord_4398624) baseStart_4398624 baseEnd_4398624 := by
    simpa [prefixWord, tailWord_4398624, baseEnd_4398624] using wordTrace_append hprefix tailTrace_4398624
  have hstable : (prefixWord ++ tailWord_4398624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398624).length < 2 ^ (prefixWord ++ tailWord_4398624).sum := by decide
  have hdescent : baseEnd_4398624 < baseStart_4398624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398750 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_4398750 : Nat := 118140960795 + 4398750 * 2 ^ 59
def prefixEnd_4398750 : Nat := 4983230072969 + 3 ^ 40 * 4398750 * 2
def baseEnd_4398750 : Nat := 752891009654923368031841

theorem tailTrace_4398750 : CollatzResearch.WordTrace tailWord_4398750 prefixEnd_4398750 752891009654923368031841 := by
  unfold tailWord_4398750
  simp only [CollatzResearch.WordTrace]
  refine ⟨20054449101760933941913213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106957061876058314356870469 20054449101760933941913213)
  ·
    refine ⟨7520418413160350228217455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20054449101760933941913213 7520418413160350228217455)
    ·
      refine ⟨11280627619740525342326183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520418413160350228217455 11280627619740525342326183)
      ·
        refine ⟨16920941429610788013489275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11280627619740525342326183 16920941429610788013489275)
        ·
          refine ⟨25381412144416182020233913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16920941429610788013489275 25381412144416182020233913)
          ·
            refine ⟨19036059108312136515175435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25381412144416182020233913 19036059108312136515175435)
            ·
              refine ⟨28554088662468204772763153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19036059108312136515175435 28554088662468204772763153)
              ·
                refine ⟨21415566496851153579572365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28554088662468204772763153 21415566496851153579572365)
                ·
                  refine ⟨8030837436319182592339637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21415566496851153579572365 8030837436319182592339637)
                  ·
                    refine ⟨752891009654923368031841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8030837436319182592339637 752891009654923368031841)
                    ·
                      rfl

theorem cell23_4398750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_4398750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398750 prefixEnd_4398750 := by exact prefixLift 4398750
  have htrace : WordTrace (prefixWord ++ tailWord_4398750) baseStart_4398750 baseEnd_4398750 := by
    simpa [prefixWord, tailWord_4398750, baseEnd_4398750] using wordTrace_append hprefix tailTrace_4398750
  have hstable : (prefixWord ++ tailWord_4398750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398750).length < 2 ^ (prefixWord ++ tailWord_4398750).sum := by decide
  have hdescent : baseEnd_4398750 < baseStart_4398750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398774 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4398774 : Nat := 118140960795 + 4398774 * 2 ^ 59
def prefixEnd_4398774 : Nat := 4983230072969 + 3 ^ 40 * 4398774 * 2
def baseEnd_4398774 : Nat := 2258685352500478010195413

theorem tailTrace_4398774 : CollatzResearch.WordTrace tailWord_4398774 prefixEnd_4398774 2258685352500478010195413 := by
  unfold tailWord_4398774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027279260375032727136211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106957645444000349089452917 10027279260375032727136211)
  ·
    refine ⟨15040918890562549090704317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10027279260375032727136211 15040918890562549090704317)
    ·
      refine ⟨5640344583960955909014119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15040918890562549090704317 5640344583960955909014119)
      ·
        refine ⟨8460516875941433863521179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5640344583960955909014119 8460516875941433863521179)
        ·
          refine ⟨12690775313912150795281769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8460516875941433863521179 12690775313912150795281769)
          ·
            refine ⟨9518081485434113096461327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12690775313912150795281769 9518081485434113096461327)
            ·
              refine ⟨14277122228151169644691991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9518081485434113096461327 14277122228151169644691991)
              ·
                refine ⟨21415683342226754467037987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14277122228151169644691991 21415683342226754467037987)
                ·
                  refine ⟨32123525013340131700556981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21415683342226754467037987 32123525013340131700556981)
                  ·
                    refine ⟨3011580470000637346927217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32123525013340131700556981 3011580470000637346927217)
                    ·
                      refine ⟨2258685352500478010195413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011580470000637346927217 2258685352500478010195413)
                      ·
                        rfl

theorem cell23_4398774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4398774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398774 prefixEnd_4398774 := by exact prefixLift 4398774
  have htrace : WordTrace (prefixWord ++ tailWord_4398774) baseStart_4398774 baseEnd_4398774 := by
    simpa [prefixWord, tailWord_4398774, baseEnd_4398774] using wordTrace_append hprefix tailTrace_4398774
  have hstable : (prefixWord ++ tailWord_4398774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398774).length < 2 ^ (prefixWord ++ tailWord_4398774).sum := by decide
  have hdescent : baseEnd_4398774 < baseStart_4398774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398776 : List Nat := [2, 1, 2, 1, 2, 1, 1, 13]
def baseStart_4398776 : Nat := 118140960795 + 4398776 * 2 ^ 59
def prefixEnd_4398776 : Nat := 4983230072969 + 3 ^ 40 * 4398776 * 2
def baseEnd_4398776 : Nat := 83655051091177296384089

theorem tailTrace_4398776 : CollatzResearch.WordTrace tailWord_4398776 prefixEnd_4398776 83655051091177296384089 := by
  unfold tailWord_4398776
  simp only [CollatzResearch.WordTrace]
  refine ⟨80218270555996638987876091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106957694074662185317168121 80218270555996638987876091)
  ·
    refine ⟨120327405833994958481814137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80218270555996638987876091 120327405833994958481814137)
    ·
      refine ⟨90245554375496218861360603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120327405833994958481814137 90245554375496218861360603)
      ·
        refine ⟨135368331563244328292040905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90245554375496218861360603 135368331563244328292040905)
        ·
          refine ⟨101526248672433246219030679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135368331563244328292040905 101526248672433246219030679)
          ·
            refine ⟨152289373008649869328546019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101526248672433246219030679 152289373008649869328546019)
            ·
              refine ⟨228434059512974803992819029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152289373008649869328546019 228434059512974803992819029)
              ·
                refine ⟨83655051091177296384089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 228434059512974803992819029 83655051091177296384089)
                ·
                  rfl

theorem cell23_4398776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 13].length) (baseStart_4398776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398776 prefixEnd_4398776 := by exact prefixLift 4398776
  have htrace : WordTrace (prefixWord ++ tailWord_4398776) baseStart_4398776 baseEnd_4398776 := by
    simpa [prefixWord, tailWord_4398776, baseEnd_4398776] using wordTrace_append hprefix tailTrace_4398776
  have hstable : (prefixWord ++ tailWord_4398776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398776).length < 2 ^ (prefixWord ++ tailWord_4398776).sum := by decide
  have hdescent : baseEnd_4398776 < baseStart_4398776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398783 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_4398783 : Nat := 118140960795 + 4398783 * 2 ^ 59
def prefixEnd_4398783 : Nat := 4983230072969 + 3 ^ 40 * 4398783 * 2
def baseEnd_4398783 : Nat := 2258689973826368474982871

theorem tailTrace_4398783 : CollatzResearch.WordTrace tailWord_4398783 prefixEnd_4398783 2258689973826368474982871 := by
  unfold tailWord_4398783
  simp only [CollatzResearch.WordTrace]
  refine ⟨160436796422967918171257003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106957864281978612114171335 160436796422967918171257003)
  ·
    refine ⟨240655194634451877256885505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160436796422967918171257003 240655194634451877256885505)
    ·
      refine ⟨180491395975838907942664129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240655194634451877256885505 180491395975838907942664129)
      ·
        refine ⟨135368546981879180956998097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180491395975838907942664129 135368546981879180956998097)
        ·
          refine ⟨101526410236409385717748573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135368546981879180956998097 101526410236409385717748573)
          ·
            refine ⟨38072403838653519644155715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101526410236409385717748573 38072403838653519644155715)
            ·
              refine ⟨57108605757980279466233573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38072403838653519644155715 57108605757980279466233573)
              ·
                refine ⟨10707863579621302399918795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57108605757980279466233573 10707863579621302399918795)
                ·
                  refine ⟨16061795369431953599878193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10707863579621302399918795 16061795369431953599878193)
                  ·
                    refine ⟨12046346527073965199908645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16061795369431953599878193 12046346527073965199908645)
                    ·
                      refine ⟨2258689973826368474982871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12046346527073965199908645 2258689973826368474982871)
                      ·
                        rfl

theorem cell23_4398783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_4398783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398783 prefixEnd_4398783 := by exact prefixLift 4398783
  have htrace : WordTrace (prefixWord ++ tailWord_4398783) baseStart_4398783 baseEnd_4398783 := by
    simpa [prefixWord, tailWord_4398783, baseEnd_4398783] using wordTrace_append hprefix tailTrace_4398783
  have hstable : (prefixWord ++ tailWord_4398783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398783).length < 2 ^ (prefixWord ++ tailWord_4398783).sum := by decide
  have hdescent : baseEnd_4398783 < baseStart_4398783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398804 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4398804 : Nat := 118140960795 + 4398804 * 2 ^ 59
def prefixEnd_4398804 : Nat := 4983230072969 + 3 ^ 40 * 4398804 * 2
def baseEnd_4398804 : Nat := 2258700756920112892820275

theorem tailTrace_4398804 : CollatzResearch.WordTrace tailWord_4398804 prefixEnd_4398804 2258700756920112892820275 := by
  unfold tailWord_4398804
  simp only [CollatzResearch.WordTrace]
  refine ⟨80218781177945919378885733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106958374903927892505180977 80218781177945919378885733)
  ·
    refine ⟨15041021470864859883541075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80218781177945919378885733 15041021470864859883541075)
    ·
      refine ⟨22561532206297289825311613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15041021470864859883541075 22561532206297289825311613)
      ·
        refine ⟨8460574577361483684491855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22561532206297289825311613 8460574577361483684491855)
        ·
          refine ⟨12690861866042225526737783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8460574577361483684491855 12690861866042225526737783)
          ·
            refine ⟨19036292799063338290106675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12690861866042225526737783 19036292799063338290106675)
            ·
              refine ⟨28554439198595007435160013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19036292799063338290106675 28554439198595007435160013)
              ·
                refine ⟨10707914699473127788185005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28554439198595007435160013 10707914699473127788185005)
                ·
                  refine ⟨4015468012302422920569377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10707914699473127788185005 4015468012302422920569377)
                  ·
                    refine ⟨3011601009226817190427033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4015468012302422920569377 3011601009226817190427033)
                    ·
                      refine ⟨2258700756920112892820275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011601009226817190427033 2258700756920112892820275)
                      ·
                        rfl

theorem cell23_4398804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4398804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398804 prefixEnd_4398804 := by exact prefixLift 4398804
  have htrace : WordTrace (prefixWord ++ tailWord_4398804) baseStart_4398804 baseEnd_4398804 := by
    simpa [prefixWord, tailWord_4398804, baseEnd_4398804] using wordTrace_append hprefix tailTrace_4398804
  have hstable : (prefixWord ++ tailWord_4398804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398804).length < 2 ^ (prefixWord ++ tailWord_4398804).sum := by decide
  have hdescent : baseEnd_4398804 < baseStart_4398804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398817 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_4398817 : Nat := 118140960795 + 4398817 * 2 ^ 59
def prefixEnd_4398817 : Nat := 4983230072969 + 3 ^ 40 * 4398817 * 2
def baseEnd_4398817 : Nat := 2258707432168621341957715

theorem tailTrace_4398817 : CollatzResearch.WordTrace tailWord_4398817 prefixEnd_4398817 2258707432168621341957715 := by
  unfold tailWord_4398817
  simp only [CollatzResearch.WordTrace]
  refine ⟨160438036504844741977994705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106958691003229827985329803 160438036504844741977994705)
  ·
    refine ⟨120328527378633556483496029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160438036504844741977994705 120328527378633556483496029)
    ·
      refine ⟨45123197766987583681311011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120328527378633556483496029 45123197766987583681311011)
      ·
        refine ⟨67684796650481375521966517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45123197766987583681311011 67684796650481375521966517)
        ·
          refine ⟨6345449685982628955184361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67684796650481375521966517 6345449685982628955184361)
          ·
            refine ⟨4759087264486971716388271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6345449685982628955184361 4759087264486971716388271)
            ·
              refine ⟨7138630896730457574582407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759087264486971716388271 7138630896730457574582407)
              ·
                refine ⟨10707946345095686361873611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7138630896730457574582407 10707946345095686361873611)
                ·
                  refine ⟨16061919517643529542810417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10707946345095686361873611 16061919517643529542810417)
                  ·
                    refine ⟨12046439638232647157107813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16061919517643529542810417 12046439638232647157107813)
                    ·
                      refine ⟨2258707432168621341957715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12046439638232647157107813 2258707432168621341957715)
                      ·
                        rfl

theorem cell23_4398817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_4398817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398817 prefixEnd_4398817 := by exact prefixLift 4398817
  have htrace : WordTrace (prefixWord ++ tailWord_4398817) baseStart_4398817 baseEnd_4398817 := by
    simpa [prefixWord, tailWord_4398817, baseEnd_4398817] using wordTrace_append hprefix tailTrace_4398817
  have hstable : (prefixWord ++ tailWord_4398817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398817).length < 2 ^ (prefixWord ++ tailWord_4398817).sum := by decide
  have hdescent : baseEnd_4398817 < baseStart_4398817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398833 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_4398833 : Nat := 118140960795 + 4398833 * 2 ^ 59
def prefixEnd_4398833 : Nat := 4983230072969 + 3 ^ 40 * 4398833 * 2
def baseEnd_4398833 : Nat := 2258715647859093279357641

theorem tailTrace_4398833 : CollatzResearch.WordTrace tailWord_4398833 prefixEnd_4398833 2258715647859093279357641 := by
  unfold tailWord_4398833
  simp only [CollatzResearch.WordTrace]
  refine ⟨160438620072786776710577153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106959080048524517807051435 160438620072786776710577153)
  ·
    refine ⟨120328965054590082532932865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160438620072786776710577153 120328965054590082532932865)
    ·
      refine ⟨90246723790942561899699649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120328965054590082532932865 90246723790942561899699649)
      ·
        refine ⟨67685042843206921424774737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90246723790942561899699649 67685042843206921424774737)
        ·
          refine ⟨50763782132405191068581053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67685042843206921424774737 50763782132405191068581053)
          ·
            refine ⟨19036418299651946650717895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50763782132405191068581053 19036418299651946650717895)
            ·
              refine ⟨28554627449477919976076843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19036418299651946650717895 28554627449477919976076843)
              ·
                refine ⟨42831941174216879964115265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28554627449477919976076843 42831941174216879964115265)
                ·
                  refine ⟨32123955880662659973086449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42831941174216879964115265 32123955880662659973086449)
                  ·
                    refine ⟨24092966910496994979814837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32123955880662659973086449 24092966910496994979814837)
                    ·
                      refine ⟨2258715647859093279357641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24092966910496994979814837 2258715647859093279357641)
                      ·
                        rfl

theorem cell23_4398833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_4398833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398833 prefixEnd_4398833 := by exact prefixLift 4398833
  have htrace : WordTrace (prefixWord ++ tailWord_4398833) baseStart_4398833 baseEnd_4398833 := by
    simpa [prefixWord, tailWord_4398833, baseEnd_4398833] using wordTrace_append hprefix tailTrace_4398833
  have hstable : (prefixWord ++ tailWord_4398833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398833).length < 2 ^ (prefixWord ++ tailWord_4398833).sum := by decide
  have hdescent : baseEnd_4398833 < baseStart_4398833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398838 : List Nat := [5, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_4398838 : Nat := 118140960795 + 4398838 * 2 ^ 59
def prefixEnd_4398838 : Nat := 4983230072969 + 3 ^ 40 * 4398838 * 2
def baseEnd_4398838 : Nat := 2258718215262365759795119

theorem tailTrace_4398838 : CollatzResearch.WordTrace tailWord_4398838 prefixEnd_4398838 2258718215262365759795119 := by
  unfold tailWord_4398838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027425152360541410281823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106959201625179108376339445 10027425152360541410281823)
  ·
    refine ⟨15041137728540812115422735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10027425152360541410281823 15041137728540812115422735)
    ·
      refine ⟨22561706592811218173134103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15041137728540812115422735 22561706592811218173134103)
      ·
        refine ⟨33842559889216827259701155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22561706592811218173134103 33842559889216827259701155)
        ·
          refine ⟨50763839833825240889551733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33842559889216827259701155 50763839833825240889551733)
          ·
            refine ⟨4759109984421116333395475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50763839833825240889551733 4759109984421116333395475)
            ·
              refine ⟨7138664976631674500093213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759109984421116333395475 7138664976631674500093213)
              ·
                refine ⟨2676999366236877937534955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7138664976631674500093213 2676999366236877937534955)
                ·
                  refine ⟨4015499049355316906302433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676999366236877937534955 4015499049355316906302433)
                  ·
                    refine ⟨3011624287016487679726825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4015499049355316906302433 3011624287016487679726825)
                    ·
                      refine ⟨2258718215262365759795119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011624287016487679726825 2258718215262365759795119)
                      ·
                        rfl

theorem cell23_4398838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_4398838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398838 prefixEnd_4398838 := by exact prefixLift 4398838
  have htrace : WordTrace (prefixWord ++ tailWord_4398838) baseStart_4398838 baseEnd_4398838 := by
    simpa [prefixWord, tailWord_4398838, baseEnd_4398838] using wordTrace_append hprefix tailTrace_4398838
  have hstable : (prefixWord ++ tailWord_4398838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398838).length < 2 ^ (prefixWord ++ tailWord_4398838).sum := by decide
  have hdescent : baseEnd_4398838 < baseStart_4398838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398847 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 1, 3, 2]
def baseStart_4398847 : Nat := 118140960795 + 4398847 * 2 ^ 59
def prefixEnd_4398847 : Nat := 4983230072969 + 3 ^ 40 * 4398847 * 2
def baseEnd_4398847 : Nat := 2258722836588256224582577

theorem tailTrace_4398847 : CollatzResearch.WordTrace tailWord_4398847 prefixEnd_4398847 2258722836588256224582577 := by
  unfold tailWord_4398847
  simp only [CollatzResearch.WordTrace]
  refine ⟨160439130694736057101586795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106959420463157371401057863 160439130694736057101586795)
  ·
    refine ⟨240658696042104085652380193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160439130694736057101586795 240658696042104085652380193)
    ·
      refine ⟨180494022031578064239285145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240658696042104085652380193 180494022031578064239285145)
      ·
        refine ⟨135370516523683548179463859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180494022031578064239285145 135370516523683548179463859)
        ·
          refine ⟨203055774785525322269195789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135370516523683548179463859 203055774785525322269195789)
          ·
            refine ⟨76145915544571995850948421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203055774785525322269195789 76145915544571995850948421)
            ·
              refine ⟨14277359164607249222052829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76145915544571995850948421 14277359164607249222052829)
              ·
                refine ⟨5354009686727718458269811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14277359164607249222052829 5354009686727718458269811)
                ·
                  refine ⟨8031014530091577687404717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354009686727718458269811 8031014530091577687404717)
                  ·
                    refine ⟨3011630448784341632776769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8031014530091577687404717 3011630448784341632776769)
                    ·
                      refine ⟨2258722836588256224582577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011630448784341632776769 2258722836588256224582577)
                      ·
                        rfl

theorem cell23_4398847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_4398847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398847 prefixEnd_4398847 := by exact prefixLift 4398847
  have htrace : WordTrace (prefixWord ++ tailWord_4398847) baseStart_4398847 baseEnd_4398847 := by
    simpa [prefixWord, tailWord_4398847, baseEnd_4398847] using wordTrace_append hprefix tailTrace_4398847
  have hstable : (prefixWord ++ tailWord_4398847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398847).length < 2 ^ (prefixWord ++ tailWord_4398847).sum := by decide
  have hdescent : baseEnd_4398847 < baseStart_4398847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398850 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4398850 : Nat := 118140960795 + 4398850 * 2 ^ 59
def prefixEnd_4398850 : Nat := 4983230072969 + 3 ^ 40 * 4398850 * 2
def baseEnd_4398850 : Nat := 2258724377030219712845063

theorem tailTrace_4398850 : CollatzResearch.WordTrace tailWord_4398850 prefixEnd_4398850 2258724377030219712845063 := by
  unfold tailWord_4398850
  simp only [CollatzResearch.WordTrace]
  refine ⟨40109810028431297153486501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106959493409150125742630669 40109810028431297153486501)
  ·
    refine ⟨7520589380330868216278719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40109810028431297153486501 7520589380330868216278719)
    ·
      refine ⟨11280884070496302324418079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520589380330868216278719 11280884070496302324418079)
      ·
        refine ⟨16921326105744453486627119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11280884070496302324418079 16921326105744453486627119)
        ·
          refine ⟨25381989158616680229940679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16921326105744453486627119 25381989158616680229940679)
          ·
            refine ⟨38072983737925020344911019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25381989158616680229940679 38072983737925020344911019)
            ·
              refine ⟨57109475606887530517366529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38072983737925020344911019 57109475606887530517366529)
              ·
                refine ⟨42832106705165647888024897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57109475606887530517366529 42832106705165647888024897)
                ·
                  refine ⟨32124080028874235916018673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42832106705165647888024897 32124080028874235916018673)
                  ·
                    refine ⟨24093060021655676937014005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32124080028874235916018673 24093060021655676937014005)
                    ·
                      refine ⟨2258724377030219712845063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24093060021655676937014005 2258724377030219712845063)
                      ·
                        rfl

theorem cell23_4398850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4398850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398850 prefixEnd_4398850 := by exact prefixLift 4398850
  have htrace : WordTrace (prefixWord ++ tailWord_4398850) baseStart_4398850 baseEnd_4398850 := by
    simpa [prefixWord, tailWord_4398850, baseEnd_4398850] using wordTrace_append hprefix tailTrace_4398850
  have hstable : (prefixWord ++ tailWord_4398850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398850).length < 2 ^ (prefixWord ++ tailWord_4398850).sum := by decide
  have hdescent : baseEnd_4398850 < baseStart_4398850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398861 : List Nat := [1, 7, 2, 1, 1, 1, 2, 8]
def baseStart_4398861 : Nat := 118140960795 + 4398861 * 2 ^ 59
def prefixEnd_4398861 : Nat := 4983230072969 + 3 ^ 40 * 4398861 * 2
def baseEnd_4398861 : Nat := 83656667604348858141019

theorem tailTrace_4398861 : CollatzResearch.WordTrace tailWord_4398861 prefixEnd_4398861 83656667604348858141019 := by
  unfold tailWord_4398861
  simp only [CollatzResearch.WordTrace]
  refine ⟨160439641316685337492596437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106959760877790224995064291 160439641316685337492596437)
  ·
    refine ⟨3760304093359812597482729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 160439641316685337492596437 3760304093359812597482729)
    ·
      refine ⟨2820228070019859448112047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3760304093359812597482729 2820228070019859448112047)
      ·
        refine ⟨4230342105029789172168071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820228070019859448112047 4230342105029789172168071)
        ·
          refine ⟨6345513157544683758252107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230342105029789172168071 6345513157544683758252107)
          ·
            refine ⟨9518269736317025637378161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6345513157544683758252107 9518269736317025637378161)
            ·
              refine ⟨7138702302237769228033621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9518269736317025637378161 7138702302237769228033621)
              ·
                refine ⟨83656667604348858141019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7138702302237769228033621 83656667604348858141019)
                ·
                  rfl

theorem cell23_4398861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 8].length) (baseStart_4398861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398861 prefixEnd_4398861 := by exact prefixLift 4398861
  have htrace : WordTrace (prefixWord ++ tailWord_4398861) baseStart_4398861 baseEnd_4398861 := by
    simpa [prefixWord, tailWord_4398861, baseEnd_4398861] using wordTrace_append hprefix tailTrace_4398861
  have hstable : (prefixWord ++ tailWord_4398861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398861).length < 2 ^ (prefixWord ++ tailWord_4398861).sum := by decide
  have hdescent : baseEnd_4398861 < baseStart_4398861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398871 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 2, 1, 3]
def baseStart_4398871 : Nat := 118140960795 + 4398871 * 2 ^ 59
def prefixEnd_4398871 : Nat := 4983230072969 + 3 ^ 40 * 4398871 * 2
def baseEnd_4398871 : Nat := 2258735160123964130682467

theorem tailTrace_4398871 : CollatzResearch.WordTrace tailWord_4398871 prefixEnd_4398871 2258735160123964130682467 := by
  unfold tailWord_4398871
  simp only [CollatzResearch.WordTrace]
  refine ⟨160440006046649109200460467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106960004031099406133640311 160440006046649109200460467)
  ·
    refine ⟨240660009069973663800690701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160440006046649109200460467 240660009069973663800690701)
    ·
      refine ⟨90247503401240123925259013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240660009069973663800690701 90247503401240123925259013)
      ·
        refine ⟨16921406887732523235986065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90247503401240123925259013 16921406887732523235986065)
        ·
          refine ⟨12691055165799392426989549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16921406887732523235986065 12691055165799392426989549)
          ·
            refine ⟨4759145687174772160121081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12691055165799392426989549 4759145687174772160121081)
            ·
              refine ⟨3569359265381079120090811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759145687174772160121081 3569359265381079120090811)
              ·
                refine ⟨5354038898071618680136217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569359265381079120090811 5354038898071618680136217)
                ·
                  refine ⟨4015529173553714010102163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354038898071618680136217 4015529173553714010102163)
                  ·
                    refine ⟨6023293760330571015153245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4015529173553714010102163 6023293760330571015153245)
                    ·
                      refine ⟨2258735160123964130682467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6023293760330571015153245 2258735160123964130682467)
                      ·
                        rfl

theorem cell23_4398871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_4398871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398871 prefixEnd_4398871 := by exact prefixLift 4398871
  have htrace : WordTrace (prefixWord ++ tailWord_4398871) baseStart_4398871 baseEnd_4398871 := by
    simpa [prefixWord, tailWord_4398871, baseEnd_4398871] using wordTrace_append hprefix tailTrace_4398871
  have hstable : (prefixWord ++ tailWord_4398871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398871).length < 2 ^ (prefixWord ++ tailWord_4398871).sum := by decide
  have hdescent : baseEnd_4398871 < baseStart_4398871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398873 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_4398873 : Nat := 118140960795 + 4398873 * 2 ^ 59
def prefixEnd_4398873 : Nat := 4983230072969 + 3 ^ 40 * 4398873 * 2
def baseEnd_4398873 : Nat := 2258736187085273122857457

theorem tailTrace_4398873 : CollatzResearch.WordTrace tailWord_4398873 prefixEnd_4398873 2258736187085273122857457 := by
  unfold tailWord_4398873
  simp only [CollatzResearch.WordTrace]
  refine ⟨160440078992641863542033273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106960052661761242361355515 160440078992641863542033273)
  ·
    refine ⟨120330059244481397656524955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160440078992641863542033273 120330059244481397656524955)
    ·
      refine ⟨180495088866722096484787433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120330059244481397656524955 180495088866722096484787433)
      ·
        refine ⟨135371316650041572363590575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180495088866722096484787433 135371316650041572363590575)
        ·
          refine ⟨203056974975062358545385863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135371316650041572363590575 203056974975062358545385863)
          ·
            refine ⟨304585462462593537818078795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203056974975062358545385863 304585462462593537818078795)
            ·
              refine ⟨456878193693890306727118193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304585462462593537818078795 456878193693890306727118193)
              ·
                refine ⟨342658645270417730045338645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456878193693890306727118193 342658645270417730045338645)
                ·
                  refine ⟨16062123997050831095875249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 342658645270417730045338645 16062123997050831095875249)
                  ·
                    refine ⟨12046592997788123321906437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16062123997050831095875249 12046592997788123321906437)
                    ·
                      refine ⟨2258736187085273122857457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12046592997788123321906437 2258736187085273122857457)
                      ·
                        rfl

theorem cell23_4398873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_4398873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398873 prefixEnd_4398873 := by exact prefixLift 4398873
  have htrace : WordTrace (prefixWord ++ tailWord_4398873) baseStart_4398873 baseEnd_4398873 := by
    simpa [prefixWord, tailWord_4398873, baseEnd_4398873] using wordTrace_append hprefix tailTrace_4398873
  have hstable : (prefixWord ++ tailWord_4398873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398873).length < 2 ^ (prefixWord ++ tailWord_4398873).sum := by decide
  have hdescent : baseEnd_4398873 < baseStart_4398873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398883 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 7]
def baseStart_4398883 : Nat := 118140960795 + 4398883 * 2 ^ 59
def prefixEnd_4398883 : Nat := 4983230072969 + 3 ^ 40 * 4398883 * 2
def baseEnd_4398883 : Nat := 250971257987979787081379

theorem tailTrace_4398883 : CollatzResearch.WordTrace tailWord_4398883 prefixEnd_4398883 250971257987979787081379 := by
  unfold tailWord_4398883
  simp only [CollatzResearch.WordTrace]
  refine ⟨160440443722605635249897303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106960295815070423499931535 160440443722605635249897303)
  ·
    refine ⟨240660665583908452874845955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160440443722605635249897303 240660665583908452874845955)
    ·
      refine ⟨360990998375862679312268933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240660665583908452874845955 360990998375862679312268933)
      ·
        refine ⟨67685812195474252371050425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360990998375862679312268933 67685812195474252371050425)
        ·
          refine ⟨50764359146605689278287819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67685812195474252371050425 50764359146605689278287819)
          ·
            refine ⟨76146538719908533917431729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50764359146605689278287819 76146538719908533917431729)
            ·
              refine ⟨57109904039931400438073797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76146538719908533917431729 57109904039931400438073797)
              ·
                refine ⟨10708107007487137582138837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57109904039931400438073797 10708107007487137582138837)
                ·
                  refine ⟨250971257987979787081379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10708107007487137582138837 250971257987979787081379)
                  ·
                    rfl

theorem cell23_4398883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 7].length) (baseStart_4398883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398883 prefixEnd_4398883 := by exact prefixLift 4398883
  have htrace : WordTrace (prefixWord ++ tailWord_4398883) baseStart_4398883 baseEnd_4398883 := by
    simpa [prefixWord, tailWord_4398883, baseEnd_4398883] using wordTrace_append hprefix tailTrace_4398883
  have hstable : (prefixWord ++ tailWord_4398883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398883).length < 2 ^ (prefixWord ++ tailWord_4398883).sum := by decide
  have hdescent : baseEnd_4398883 < baseStart_4398883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398911 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 2, 2, 2]
def baseStart_4398911 : Nat := 118140960795 + 4398911 * 2 ^ 59
def prefixEnd_4398911 : Nat := 4983230072969 + 3 ^ 40 * 4398911 * 2
def baseEnd_4398911 : Nat := 2258755699350143974182283

theorem tailTrace_4398911 : CollatzResearch.WordTrace tailWord_4398911 prefixEnd_4398911 2258755699350143974182283 := by
  unfold tailWord_4398911
  simp only [CollatzResearch.WordTrace]
  refine ⟨160441464966504196031916587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106960976644336130687944391 160441464966504196031916587)
  ·
    refine ⟨240662197449756294047874881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160441464966504196031916587 240662197449756294047874881)
    ·
      refine ⟨180496648087317220535906161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240662197449756294047874881 180496648087317220535906161)
      ·
        refine ⟨135372486065487915401929621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180496648087317220535906161 135372486065487915401929621)
        ·
          refine ⟨6345585284319746034465451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135372486065487915401929621 6345585284319746034465451)
          ·
            refine ⟨9518377926479619051698177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6345585284319746034465451 9518377926479619051698177)
            ·
              refine ⟨7138783444859714288773633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9518377926479619051698177 7138783444859714288773633)
              ·
                refine ⟨5354087583644785716580225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7138783444859714288773633 5354087583644785716580225)
                ·
                  refine ⟨4015565687733589287435169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354087583644785716580225 4015565687733589287435169)
                  ·
                    refine ⟨3011674265800191965576377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4015565687733589287435169 3011674265800191965576377)
                    ·
                      refine ⟨2258755699350143974182283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011674265800191965576377 2258755699350143974182283)
                      ·
                        rfl

theorem cell23_4398911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_4398911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398911 prefixEnd_4398911 := by exact prefixLift 4398911
  have htrace : WordTrace (prefixWord ++ tailWord_4398911) baseStart_4398911 baseEnd_4398911 := by
    simpa [prefixWord, tailWord_4398911, baseEnd_4398911] using wordTrace_append hprefix tailTrace_4398911
  have hstable : (prefixWord ++ tailWord_4398911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398911).length < 2 ^ (prefixWord ++ tailWord_4398911).sum := by decide
  have hdescent : baseEnd_4398911 < baseStart_4398911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398960 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 7, 4]
def baseStart_4398960 : Nat := 118140960795 + 4398960 * 2 ^ 59
def prefixEnd_4398960 : Nat := 4983230072969 + 3 ^ 40 * 4398960 * 2
def baseEnd_4398960 : Nat := 752926953300738094156519

theorem tailTrace_4398960 : CollatzResearch.WordTrace tailWord_4398960 prefixEnd_4398960 752926953300738094156519 := by
  unfold tailWord_4398960
  simp only [CollatzResearch.WordTrace]
  refine ⟨80221626071663338700225167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106962168095551118266966889 80221626071663338700225167)
  ·
    refine ⟨120332439107495008050337751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80221626071663338700225167 120332439107495008050337751)
    ·
      refine ⟨180498658661242512075506627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120332439107495008050337751 180498658661242512075506627)
      ·
        refine ⟨270747987991863768113259941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180498658661242512075506627 270747987991863768113259941)
        ·
          refine ⟨50765247748474456521236239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270747987991863768113259941 50765247748474456521236239)
          ·
            refine ⟨76147871622711684781854359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50765247748474456521236239 76147871622711684781854359)
            ·
              refine ⟨114221807434067527172781539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76147871622711684781854359 114221807434067527172781539)
              ·
                refine ⟨171332711151101290759172309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114221807434067527172781539 171332711151101290759172309)
                ·
                  refine ⟨4015610417603936502168101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 171332711151101290759172309 4015610417603936502168101)
                  ·
                    refine ⟨752926953300738094156519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015610417603936502168101 752926953300738094156519)
                    ·
                      rfl

theorem cell23_4398960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_4398960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398960 prefixEnd_4398960 := by exact prefixLift 4398960
  have htrace : WordTrace (prefixWord ++ tailWord_4398960) baseStart_4398960 baseEnd_4398960 := by
    simpa [prefixWord, tailWord_4398960, baseEnd_4398960] using wordTrace_append hprefix tailTrace_4398960
  have hstable : (prefixWord ++ tailWord_4398960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398960).length < 2 ^ (prefixWord ++ tailWord_4398960).sum := by decide
  have hdescent : baseEnd_4398960 < baseStart_4398960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4398994 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_4398994 : Nat := 118140960795 + 4398994 * 2 ^ 59
def prefixEnd_4398994 : Nat := 4983230072969 + 3 ^ 40 * 4398994 * 2
def baseEnd_4398994 : Nat := 752932772748155716481467

theorem tailTrace_4398994 : CollatzResearch.WordTrace tailWord_4398994 prefixEnd_4398994 752932772748155716481467 := by
  unfold tailWord_4398994
  simp only [CollatzResearch.WordTrace]
  refine ⟨40111123056300875301797009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106962994816802334138125357 40111123056300875301797009)
  ·
    refine ⟨30083342292225656476347757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40111123056300875301797009 30083342292225656476347757)
    ·
      refine ⟨11281253359584621178630409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30083342292225656476347757 11281253359584621178630409)
      ·
        refine ⟨8460940019688465883972807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11281253359584621178630409 8460940019688465883972807)
        ·
          refine ⟨12691410029532698825959211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8460940019688465883972807 12691410029532698825959211)
          ·
            refine ⟨19037115044299048238938817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12691410029532698825959211 19037115044299048238938817)
            ·
              refine ⟨14277836283224286179204113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19037115044299048238938817 14277836283224286179204113)
              ·
                refine ⟨10708377212418214634403085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14277836283224286179204113 10708377212418214634403085)
                ·
                  refine ⟨4015641454656830487901157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10708377212418214634403085 4015641454656830487901157)
                  ·
                    refine ⟨752932772748155716481467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015641454656830487901157 752932772748155716481467)
                    ·
                      rfl

theorem cell23_4398994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_4398994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4398994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4398994 prefixEnd_4398994 := by exact prefixLift 4398994
  have htrace : WordTrace (prefixWord ++ tailWord_4398994) baseStart_4398994 baseEnd_4398994 := by
    simpa [prefixWord, tailWord_4398994, baseEnd_4398994] using wordTrace_append hprefix tailTrace_4398994
  have hstable : (prefixWord ++ tailWord_4398994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4398994).length < 2 ^ (prefixWord ++ tailWord_4398994).sum := by decide
  have hdescent : baseEnd_4398994 < baseStart_4398994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4398994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399028 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4399028 : Nat := 118140960795 + 4399028 * 2 ^ 59
def prefixEnd_4399028 : Nat := 4983230072969 + 3 ^ 40 * 4399028 * 2
def baseEnd_4399028 : Nat := 752938592195573338806415

theorem tailTrace_4399028 : CollatzResearch.WordTrace tailWord_4399028 prefixEnd_4399028 752938592195573338806415 := by
  unfold tailWord_4399028
  simp only [CollatzResearch.WordTrace]
  refine ⟨80222866153540162506962869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106963821538053550009283825 80222866153540162506962869)
  ·
    refine ⟨7520893701894390235027769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80222866153540162506962869 7520893701894390235027769)
    ·
      refine ⟨5640670276420792676270827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7520893701894390235027769 5640670276420792676270827)
      ·
        refine ⟨8461005414631189014406241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5640670276420792676270827 8461005414631189014406241)
        ·
          refine ⟨6345754060973391760804681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8461005414631189014406241 6345754060973391760804681)
          ·
            refine ⟨4759315545730043820603511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6345754060973391760804681 4759315545730043820603511)
            ·
              refine ⟨7138973318595065730905267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759315545730043820603511 7138973318595065730905267)
              ·
                refine ⟨10708459977892598596357901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7138973318595065730905267 10708459977892598596357901)
                ·
                  refine ⟨4015672491709724473634213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10708459977892598596357901 4015672491709724473634213)
                  ·
                    refine ⟨752938592195573338806415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4015672491709724473634213 752938592195573338806415)
                    ·
                      rfl

theorem cell23_4399028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4399028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399028 prefixEnd_4399028 := by exact prefixLift 4399028
  have htrace : WordTrace (prefixWord ++ tailWord_4399028) baseStart_4399028 baseEnd_4399028 := by
    simpa [prefixWord, tailWord_4399028, baseEnd_4399028] using wordTrace_append hprefix tailTrace_4399028
  have hstable : (prefixWord ++ tailWord_4399028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399028).length < 2 ^ (prefixWord ++ tailWord_4399028).sum := by decide
  have hdescent : baseEnd_4399028 < baseStart_4399028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399057 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_4399057 : Nat := 118140960795 + 4399057 * 2 ^ 59
def prefixEnd_4399057 : Nat := 4983230072969 + 3 ^ 40 * 4399057 * 2
def baseEnd_4399057 : Nat := 2258830667525700402956611

theorem tailTrace_4399057 : CollatzResearch.WordTrace tailWord_4399057 prefixEnd_4399057 2258830667525700402956611 := by
  unfold tailWord_4399057
  simp only [CollatzResearch.WordTrace]
  refine ⟨160446790023975262966731425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106964526682650175311154283 160446790023975262966731425)
  ·
    refine ⟨120335092517981447225048569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160446790023975262966731425 120335092517981447225048569)
    ·
      refine ⟨90251319388486085418786427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120335092517981447225048569 90251319388486085418786427)
      ·
        refine ⟨135376979082729128128179641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90251319388486085418786427 135376979082729128128179641)
        ·
          refine ⟨101532734312046846096134731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135376979082729128128179641 101532734312046846096134731)
          ·
            refine ⟨152299101468070269144202097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101532734312046846096134731 152299101468070269144202097)
            ·
              refine ⟨114224326101052701858151573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152299101468070269144202097 114224326101052701858151573)
              ·
                refine ⟨5354265285986845399600855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114224326101052701858151573 5354265285986845399600855)
                ·
                  refine ⟨8031397928980268099401283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354265285986845399600855 8031397928980268099401283)
                  ·
                    refine ⟨12047096893470402149101925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8031397928980268099401283 12047096893470402149101925)
                    ·
                      refine ⟨2258830667525700402956611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12047096893470402149101925 2258830667525700402956611)
                      ·
                        rfl

theorem cell23_4399057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_4399057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399057 prefixEnd_4399057 := by exact prefixLift 4399057
  have htrace : WordTrace (prefixWord ++ tailWord_4399057) baseStart_4399057 baseEnd_4399057 := by
    simpa [prefixWord, tailWord_4399057, baseEnd_4399057] using wordTrace_append hprefix tailTrace_4399057
  have hstable : (prefixWord ++ tailWord_4399057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399057).length < 2 ^ (prefixWord ++ tailWord_4399057).sum := by decide
  have hdescent : baseEnd_4399057 < baseStart_4399057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399061 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4399061 : Nat := 118140960795 + 4399061 * 2 ^ 59
def prefixEnd_4399061 : Nat := 4983230072969 + 3 ^ 40 * 4399061 * 2
def baseEnd_4399061 : Nat := 2258832721448318387306593

theorem tailTrace_4399061 : CollatzResearch.WordTrace tailWord_4399061 prefixEnd_4399061 2258832721448318387306593 := by
  unfold tailWord_4399061
  simp only [CollatzResearch.WordTrace]
  refine ⟨160446935915960771649877037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106964623943973847766584691 160446935915960771649877037)
  ·
    refine ⟨60167600968485289368703889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160446935915960771649877037 60167600968485289368703889)
    ·
      refine ⟨45125700726363967026527917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60167600968485289368703889 45125700726363967026527917)
      ·
        refine ⟨16922137772386487634947969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45125700726363967026527917 16922137772386487634947969)
        ·
          refine ⟨12691603329289865726210977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16922137772386487634947969 12691603329289865726210977)
          ·
            refine ⟨9518702496967399294658233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12691603329289865726210977 9518702496967399294658233)
            ·
              refine ⟨7139026872725549470993675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9518702496967399294658233 7139026872725549470993675)
              ·
                refine ⟨10708540309088324206490513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139026872725549470993675 10708540309088324206490513)
                ·
                  refine ⟨8031405231816243154867885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10708540309088324206490513 8031405231816243154867885)
                  ·
                    refine ⟨3011776961931091183075457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8031405231816243154867885 3011776961931091183075457)
                    ·
                      refine ⟨2258832721448318387306593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011776961931091183075457 2258832721448318387306593)
                      ·
                        rfl

theorem cell23_4399061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4399061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399061 prefixEnd_4399061 := by exact prefixLift 4399061
  have htrace : WordTrace (prefixWord ++ tailWord_4399061) baseStart_4399061 baseEnd_4399061 := by
    simpa [prefixWord, tailWord_4399061, baseEnd_4399061] using wordTrace_append hprefix tailTrace_4399061
  have hstable : (prefixWord ++ tailWord_4399061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399061).length < 2 ^ (prefixWord ++ tailWord_4399061).sum := by decide
  have hdescent : baseEnd_4399061 < baseStart_4399061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399085 : List Nat := [1, 5, 1, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4399085 : Nat := 118140960795 + 4399085 * 2 ^ 59
def prefixEnd_4399085 : Nat := 4983230072969 + 3 ^ 40 * 4399085 * 2
def baseEnd_4399085 : Nat := 2258845044984026293406483

theorem tailTrace_4399085 : CollatzResearch.WordTrace tailWord_4399085 prefixEnd_4399085 2258845044984026293406483 := by
  unfold tailWord_4399085
  simp only [CollatzResearch.WordTrace]
  refine ⟨160447811267873823748750709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106965207511915882499167139 160447811267873823748750709)
  ·
    refine ⟨15041982306363170976445379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160447811267873823748750709 15041982306363170976445379)
    ·
      refine ⟨22562973459544756464668069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15041982306363170976445379 22562973459544756464668069)
      ·
        refine ⟨4230557523664641837125263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22562973459544756464668069 4230557523664641837125263)
        ·
          refine ⟨6345836285496962755687895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230557523664641837125263 6345836285496962755687895)
          ·
            refine ⟨9518754428245444133531843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6345836285496962755687895 9518754428245444133531843)
            ·
              refine ⟨14278131642368166200297765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9518754428245444133531843 14278131642368166200297765)
              ·
                refine ⟨2677149682944031162555831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14278131642368166200297765 2677149682944031162555831)
                ·
                  refine ⟨4015724524416046743833747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677149682944031162555831 4015724524416046743833747)
                  ·
                    refine ⟨6023586786624070115750621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4015724524416046743833747 6023586786624070115750621)
                    ·
                      refine ⟨2258845044984026293406483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6023586786624070115750621 2258845044984026293406483)
                      ·
                        rfl

theorem cell23_4399085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4399085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399085 prefixEnd_4399085 := by exact prefixLift 4399085
  have htrace : WordTrace (prefixWord ++ tailWord_4399085) baseStart_4399085 baseEnd_4399085 := by
    simpa [prefixWord, tailWord_4399085, baseEnd_4399085] using wordTrace_append hprefix tailTrace_4399085
  have hstable : (prefixWord ++ tailWord_4399085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399085).length < 2 ^ (prefixWord ++ tailWord_4399085).sum := by decide
  have hdescent : baseEnd_4399085 < baseStart_4399085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399097 : List Nat := [1, 2, 1, 3, 1, 6, 1, 8]
def baseStart_4399097 : Nat := 118140960795 + 4399097 * 2 ^ 59
def prefixEnd_4399097 : Nat := 4983230072969 + 3 ^ 40 * 4399097 * 2
def baseEnd_4399097 : Nat := 83661155805625194313201

theorem tailTrace_4399097 : CollatzResearch.WordTrace tailWord_4399097 prefixEnd_4399097 83661155805625194313201 := by
  unfold tailWord_4399097
  simp only [CollatzResearch.WordTrace]
  refine ⟨160448248943830349798187545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106965499295886899865458363 160448248943830349798187545)
  ·
    refine ⟨120336186707872762348640659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160448248943830349798187545 120336186707872762348640659)
    ·
      refine ⟨180504280061809143522960989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120336186707872762348640659 180504280061809143522960989)
      ·
        refine ⟨67689105023178428821110371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180504280061809143522960989 67689105023178428821110371)
        ·
          refine ⟨101533657534767643231665557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67689105023178428821110371 101533657534767643231665557)
          ·
            refine ⟨4759390196942233276484323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101533657534767643231665557 4759390196942233276484323)
            ·
              refine ⟨7139085295413349914726485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759390196942233276484323 7139085295413349914726485)
              ·
                refine ⟨83661155805625194313201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7139085295413349914726485 83661155805625194313201)
                ·
                  rfl

theorem cell23_4399097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 8].length) (baseStart_4399097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399097 prefixEnd_4399097 := by exact prefixLift 4399097
  have htrace : WordTrace (prefixWord ++ tailWord_4399097) baseStart_4399097 baseEnd_4399097 := by
    simpa [prefixWord, tailWord_4399097, baseEnd_4399097] using wordTrace_append hprefix tailTrace_4399097
  have hstable : (prefixWord ++ tailWord_4399097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399097).length < 2 ^ (prefixWord ++ tailWord_4399097).sum := by decide
  have hdescent : baseEnd_4399097 < baseStart_4399097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399114 : List Nat := [3, 1, 2, 2, 4, 1, 3, 7]
def baseStart_4399114 : Nat := 118140960795 + 4399114 * 2 ^ 59
def prefixEnd_4399114 : Nat := 4983230072969 + 3 ^ 40 * 4399114 * 2
def baseEnd_4399114 : Nat := 83661479108259506664587

theorem tailTrace_4399114 : CollatzResearch.WordTrace tailWord_4399114 prefixEnd_4399114 83661479108259506664587 := by
  unfold tailWord_4399114
  simp only [CollatzResearch.WordTrace]
  refine ⟨40112217246192190425389099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106965912656512507801037597 40112217246192190425389099)
  ·
    refine ⟨60168325869288285638083649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40112217246192190425389099 60168325869288285638083649)
    ·
      refine ⟨45126244401966214228562737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60168325869288285638083649 45126244401966214228562737)
      ·
        refine ⟨33844683301474660671422053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45126244401966214228562737 33844683301474660671422053)
        ·
          refine ⟨6345878119026498875891635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33844683301474660671422053 6345878119026498875891635)
          ·
            refine ⟨9518817178539748313837453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6345878119026498875891635 9518817178539748313837453)
            ·
              refine ⟨3569556441952405617689045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9518817178539748313837453 3569556441952405617689045)
              ·
                refine ⟨83661479108259506664587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3569556441952405617689045 83661479108259506664587)
                ·
                  rfl

theorem cell23_4399114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_4399114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399114 prefixEnd_4399114 := by exact prefixLift 4399114
  have htrace : WordTrace (prefixWord ++ tailWord_4399114) baseStart_4399114 baseEnd_4399114 := by
    simpa [prefixWord, tailWord_4399114, baseEnd_4399114] using wordTrace_append hprefix tailTrace_4399114
  have hstable : (prefixWord ++ tailWord_4399114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399114).length < 2 ^ (prefixWord ++ tailWord_4399114).sum := by decide
  have hdescent : baseEnd_4399114 < baseStart_4399114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399120 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_4399120 : Nat := 118140960795 + 4399120 * 2 ^ 59
def prefixEnd_4399120 : Nat := 4983230072969 + 3 ^ 40 * 4399120 * 2
def baseEnd_4399120 : Nat := 2258863016806933656468821

theorem tailTrace_4399120 : CollatzResearch.WordTrace tailWord_4399120 prefixEnd_4399120 2258863016806933656468821 := by
  unfold tailWord_4399120
  simp only [CollatzResearch.WordTrace]
  refine ⟨80224543911373512363137407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106966058548498016484183209 80224543911373512363137407)
  ·
    refine ⟨120336815867060268544706111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80224543911373512363137407 120336815867060268544706111)
    ·
      refine ⟨180505223800590402817059167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120336815867060268544706111 180505223800590402817059167)
      ·
        refine ⟨270757835700885604225588751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180505223800590402817059167 270757835700885604225588751)
        ·
          refine ⟨406136753551328406338383127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270757835700885604225588751 406136753551328406338383127)
          ·
            refine ⟨609205130326992609507574691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406136753551328406338383127 609205130326992609507574691)
            ·
              refine ⟨913807695490488914261362037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609205130326992609507574691 913807695490488914261362037)
              ·
                refine ⟨85669471452233335712002691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 913807695490488914261362037 85669471452233335712002691)
                ·
                  refine ⟨128504207178350003568004037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85669471452233335712002691 128504207178350003568004037)
                  ·
                    refine ⟨24094538845940625669000757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 128504207178350003568004037 24094538845940625669000757)
                    ·
                      refine ⟨2258863016806933656468821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24094538845940625669000757 2258863016806933656468821)
                      ·
                        rfl

theorem cell23_4399120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_4399120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399120 prefixEnd_4399120 := by exact prefixLift 4399120
  have htrace : WordTrace (prefixWord ++ tailWord_4399120) baseStart_4399120 baseEnd_4399120 := by
    simpa [prefixWord, tailWord_4399120, baseEnd_4399120] using wordTrace_append hprefix tailTrace_4399120
  have hstable : (prefixWord ++ tailWord_4399120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399120).length < 2 ^ (prefixWord ++ tailWord_4399120).sum := by decide
  have hdescent : baseEnd_4399120 < baseStart_4399120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399125 : List Nat := [1, 3, 2, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_4399125 : Nat := 118140960795 + 4399125 * 2 ^ 59
def prefixEnd_4399125 : Nat := 4983230072969 + 3 ^ 40 * 4399125 * 2
def baseEnd_4399125 : Nat := 2258865584210206136906299

theorem tailTrace_4399125 : CollatzResearch.WordTrace tailWord_4399125 prefixEnd_4399125 2258865584210206136906299 := by
  unfold tailWord_4399125
  simp only [CollatzResearch.WordTrace]
  refine ⟨160449270187728910580206829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106966180125152607053471219 160449270187728910580206829)
  ·
    refine ⟨60168476320398341467577561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160449270187728910580206829 60168476320398341467577561)
    ·
      refine ⟨45126357240298756100683171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60168476320398341467577561 45126357240298756100683171)
      ·
        refine ⟨67689535860448134151024757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45126357240298756100683171 67689535860448134151024757)
        ·
          refine ⟨6345893986917012576658571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67689535860448134151024757 6345893986917012576658571)
          ·
            refine ⟨9518840980375518864987857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6345893986917012576658571 9518840980375518864987857)
            ·
              refine ⟨7139130735281639148740893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9518840980375518864987857 7139130735281639148740893)
              ·
                refine ⟨2677174025730614680777835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7139130735281639148740893 2677174025730614680777835)
                ·
                  refine ⟨4015761038595922021166753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677174025730614680777835 4015761038595922021166753)
                  ·
                    refine ⟨3011820778946941515875065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4015761038595922021166753 3011820778946941515875065)
                    ·
                      refine ⟨2258865584210206136906299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011820778946941515875065 2258865584210206136906299)
                      ·
                        rfl

theorem cell23_4399125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_4399125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399125 prefixEnd_4399125 := by exact prefixLift 4399125
  have htrace : WordTrace (prefixWord ++ tailWord_4399125) baseStart_4399125 baseEnd_4399125 := by
    simpa [prefixWord, tailWord_4399125, baseEnd_4399125] using wordTrace_append hprefix tailTrace_4399125
  have hstable : (prefixWord ++ tailWord_4399125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399125).length < 2 ^ (prefixWord ++ tailWord_4399125).sum := by decide
  have hdescent : baseEnd_4399125 < baseStart_4399125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399141 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_4399141 : Nat := 118140960795 + 4399141 * 2 ^ 59
def prefixEnd_4399141 : Nat := 4983230072969 + 3 ^ 40 * 4399141 * 2
def baseEnd_4399141 : Nat := 2258873799900678074306225

theorem tailTrace_4399141 : CollatzResearch.WordTrace tailWord_4399141 prefixEnd_4399141 2258873799900678074306225 := by
  unfold tailWord_4399141
  simp only [CollatzResearch.WordTrace]
  refine ⟨160449853755670945312789277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106966569170447296875192851 160449853755670945312789277)
  ·
    refine ⟨60168695158376604492295979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160449853755670945312789277 60168695158376604492295979)
    ·
      refine ⟨90253042737564906738443969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60168695158376604492295979 90253042737564906738443969)
      ·
        refine ⟨67689782053173680053832977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90253042737564906738443969 67689782053173680053832977)
        ·
          refine ⟨50767336539880260040374733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67689782053173680053832977 50767336539880260040374733)
          ·
            refine ⟨19037751202455097515140525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50767336539880260040374733 19037751202455097515140525)
            ·
              refine ⟨7139156700920661568177697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19037751202455097515140525 7139156700920661568177697)
              ·
                refine ⟨5354367525690496176133273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7139156700920661568177697 5354367525690496176133273)
                ·
                  refine ⟨4015775644267872132099955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354367525690496176133273 4015775644267872132099955)
                  ·
                    refine ⟨6023663466401808198149933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4015775644267872132099955 6023663466401808198149933)
                    ·
                      refine ⟨2258873799900678074306225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6023663466401808198149933 2258873799900678074306225)
                      ·
                        rfl

theorem cell23_4399141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_4399141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399141 prefixEnd_4399141 := by exact prefixLift 4399141
  have htrace : WordTrace (prefixWord ++ tailWord_4399141) baseStart_4399141 baseEnd_4399141 := by
    simpa [prefixWord, tailWord_4399141, baseEnd_4399141] using wordTrace_append hprefix tailTrace_4399141
  have hstable : (prefixWord ++ tailWord_4399141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399141).length < 2 ^ (prefixWord ++ tailWord_4399141).sum := by decide
  have hdescent : baseEnd_4399141 < baseStart_4399141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399157 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_4399157 : Nat := 118140960795 + 4399157 * 2 ^ 59
def prefixEnd_4399157 : Nat := 4983230072969 + 3 ^ 40 * 4399157 * 2
def baseEnd_4399157 : Nat := 752960671863716670568717

theorem tailTrace_4399157 : CollatzResearch.WordTrace tailWord_4399157 prefixEnd_4399157 752960671863716670568717 := by
  unfold tailWord_4399157
  simp only [CollatzResearch.WordTrace]
  refine ⟨160450437323612980045371725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106966958215741986696914483 160450437323612980045371725)
  ·
    refine ⟨60168913996354867517014397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160450437323612980045371725 60168913996354867517014397)
    ·
      refine ⟨22563342748633075318880399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60168913996354867517014397 22563342748633075318880399)
      ·
        refine ⟨33845014122949612978320599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22563342748633075318880399 33845014122949612978320599)
        ·
          refine ⟨50767521184424419467480899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33845014122949612978320599 50767521184424419467480899)
          ·
            refine ⟨76151281776636629201221349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50767521184424419467480899 76151281776636629201221349)
            ·
              refine ⟨14278365333119367975229003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76151281776636629201221349 14278365333119367975229003)
              ·
                refine ⟨21417547999679051962843505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14278365333119367975229003 21417547999679051962843505)
                ·
                  refine ⟨16063160999759288972132629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21417547999679051962843505 16063160999759288972132629)
                  ·
                    refine ⟨752960671863716670568717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16063160999759288972132629 752960671863716670568717)
                    ·
                      rfl

theorem cell23_4399157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_4399157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399157 prefixEnd_4399157 := by exact prefixLift 4399157
  have htrace : WordTrace (prefixWord ++ tailWord_4399157) baseStart_4399157 baseEnd_4399157 := by
    simpa [prefixWord, tailWord_4399157, baseEnd_4399157] using wordTrace_append hprefix tailTrace_4399157
  have hstable : (prefixWord ++ tailWord_4399157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399157).length < 2 ^ (prefixWord ++ tailWord_4399157).sum := by decide
  have hdescent : baseEnd_4399157 < baseStart_4399157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399167 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 3]
def baseStart_4399167 : Nat := 118140960795 + 4399167 * 2 ^ 59
def prefixEnd_4399167 : Nat := 4983230072969 + 3 ^ 40 * 4399167 * 2
def baseEnd_4399167 : Nat := 2258887150397694972581105

theorem tailTrace_4399167 : CollatzResearch.WordTrace tailWord_4399167 prefixEnd_4399167 2258887150397694972581105 := by
  unfold tailWord_4399167
  simp only [CollatzResearch.WordTrace]
  refine ⟨160450802053576751753235755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106967201369051167835490503 160450802053576751753235755)
  ·
    refine ⟨240676203080365127629853633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160450802053576751753235755 240676203080365127629853633)
    ·
      refine ⟨180507152310273845722390225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240676203080365127629853633 180507152310273845722390225)
      ·
        refine ⟨135380364232705384291792669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180507152310273845722390225 135380364232705384291792669)
        ·
          refine ⟨50767636587264519109422251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135380364232705384291792669 50767636587264519109422251)
          ·
            refine ⟨76151454880896778664133377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50767636587264519109422251 76151454880896778664133377)
            ·
              refine ⟨57113591160672583998100033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76151454880896778664133377 57113591160672583998100033)
              ·
                refine ⟨42835193370504437998575025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57113591160672583998100033 42835193370504437998575025)
                ·
                  refine ⟨32126395027878328498931269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42835193370504437998575025 32126395027878328498931269)
                  ·
                    refine ⟨6023699067727186593549613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32126395027878328498931269 6023699067727186593549613)
                    ·
                      refine ⟨2258887150397694972581105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6023699067727186593549613 2258887150397694972581105)
                      ·
                        rfl

theorem cell23_4399167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_4399167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399167 prefixEnd_4399167 := by exact prefixLift 4399167
  have htrace : WordTrace (prefixWord ++ tailWord_4399167) baseStart_4399167 baseEnd_4399167 := by
    simpa [prefixWord, tailWord_4399167, baseEnd_4399167] using wordTrace_append hprefix tailTrace_4399167
  have hstable : (prefixWord ++ tailWord_4399167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399167).length < 2 ^ (prefixWord ++ tailWord_4399167).sum := by decide
  have hdescent : baseEnd_4399167 < baseStart_4399167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399181 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_4399181 : Nat := 118140960795 + 4399181 * 2 ^ 59
def prefixEnd_4399181 : Nat := 4983230072969 + 3 ^ 40 * 4399181 * 2
def baseEnd_4399181 : Nat := 2258894339126857917806041

theorem tailTrace_4399181 : CollatzResearch.WordTrace tailWord_4399181 prefixEnd_4399181 2258894339126857917806041 := by
  unfold tailWord_4399181
  simp only [CollatzResearch.WordTrace]
  refine ⟨160451312675526032144245397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106967541783684021429496931 160451312675526032144245397)
  ·
    refine ⟨7521155281665282756761503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 160451312675526032144245397 7521155281665282756761503)
    ·
      refine ⟨11281732922497924135142255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7521155281665282756761503 11281732922497924135142255)
      ·
        refine ⟨16922599383746886202713383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11281732922497924135142255 16922599383746886202713383)
        ·
          refine ⟨25383899075620329304070075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16922599383746886202713383 25383899075620329304070075)
          ·
            refine ⟨38075848613430493956105113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25383899075620329304070075 38075848613430493956105113)
            ·
              refine ⟨28556886460072870467078835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38075848613430493956105113 28556886460072870467078835)
              ·
                refine ⟨42835329690109305700618253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28556886460072870467078835 42835329690109305700618253)
                ·
                  refine ⟨16063248633790989637731845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42835329690109305700618253 16063248633790989637731845)
                  ·
                    refine ⟨3011859118835810557074721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16063248633790989637731845 3011859118835810557074721)
                    ·
                      refine ⟨2258894339126857917806041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011859118835810557074721 2258894339126857917806041)
                      ·
                        rfl

theorem cell23_4399181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_4399181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399181 prefixEnd_4399181 := by exact prefixLift 4399181
  have htrace : WordTrace (prefixWord ++ tailWord_4399181) baseStart_4399181 baseEnd_4399181 := by
    simpa [prefixWord, tailWord_4399181, baseEnd_4399181] using wordTrace_append hprefix tailTrace_4399181
  have hstable : (prefixWord ++ tailWord_4399181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399181).length < 2 ^ (prefixWord ++ tailWord_4399181).sum := by decide
  have hdescent : baseEnd_4399181 < baseStart_4399181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399204 : List Nat := [2, 3, 1, 1, 2, 1, 2, 6, 5]
def baseStart_4399204 : Nat := 118140960795 + 4399204 * 2 ^ 59
def prefixEnd_4399204 : Nat := 4983230072969 + 3 ^ 40 * 4399204 * 2
def baseEnd_4399204 : Nat := 250989572131323480868715

theorem tailTrace_4399204 : CollatzResearch.WordTrace tailWord_4399204 prefixEnd_4399204 250989572131323480868715 := by
  unfold tailWord_4399204
  simp only [CollatzResearch.WordTrace]
  refine ⟨80226075777221353536166333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106968101036295138048221777 80226075777221353536166333)
  ·
    refine ⟨30084778416458007576062375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80226075777221353536166333 30084778416458007576062375)
    ·
      refine ⟨45127167624687011364093563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30084778416458007576062375 45127167624687011364093563)
      ·
        refine ⟨67690751437030517046140345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45127167624687011364093563 67690751437030517046140345)
        ·
          refine ⟨50768063577772887784605259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67690751437030517046140345 50768063577772887784605259)
          ·
            refine ⟨76152095366659331676907889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50768063577772887784605259 76152095366659331676907889)
            ·
              refine ⟨57114071524994498757680917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76152095366659331676907889 57114071524994498757680917)
              ·
                refine ⟨2677222102734117129266293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57114071524994498757680917 2677222102734117129266293)
                ·
                  refine ⟨250989572131323480868715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677222102734117129266293 250989572131323480868715)
                  ·
                    rfl

theorem cell23_4399204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_4399204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399204 prefixEnd_4399204 := by exact prefixLift 4399204
  have htrace : WordTrace (prefixWord ++ tailWord_4399204) baseStart_4399204 baseEnd_4399204 := by
    simpa [prefixWord, tailWord_4399204, baseEnd_4399204] using wordTrace_append hprefix tailTrace_4399204
  have hstable : (prefixWord ++ tailWord_4399204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399204).length < 2 ^ (prefixWord ++ tailWord_4399204).sum := by decide
  have hdescent : baseEnd_4399204 < baseStart_4399204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399214 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_4399214 : Nat := 118140960795 + 4399214 * 2 ^ 59
def prefixEnd_4399214 : Nat := 4983230072969 + 3 ^ 40 * 4399214 * 2
def baseEnd_4399214 : Nat := 2258911283988456288693389

theorem tailTrace_4399214 : CollatzResearch.WordTrace tailWord_4399214 prefixEnd_4399214 2258911283988456288693389 := by
  unfold tailWord_4399214
  simp only [CollatzResearch.WordTrace]
  refine ⟨20056564535550809847524587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106968344189604319186797797 20056564535550809847524587)
  ·
    refine ⟨30084846803326214771286881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20056564535550809847524587 30084846803326214771286881)
    ·
      refine ⟨22563635102494661078465161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30084846803326214771286881 22563635102494661078465161)
      ·
        refine ⟨16922726326870995808848871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22563635102494661078465161 16922726326870995808848871)
        ·
          refine ⟨25384089490306493713273307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16922726326870995808848871 25384089490306493713273307)
          ·
            refine ⟨38076134235459740569909961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25384089490306493713273307 38076134235459740569909961)
            ·
              refine ⟨28557100676594805427432471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38076134235459740569909961 28557100676594805427432471)
              ·
                refine ⟨42835651014892208141148707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28557100676594805427432471 42835651014892208141148707)
                ·
                  refine ⟨64253476522338312211723061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42835651014892208141148707 64253476522338312211723061)
                  ·
                    refine ⟨6023763423969216769849037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64253476522338312211723061 6023763423969216769849037)
                    ·
                      refine ⟨2258911283988456288693389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6023763423969216769849037 2258911283988456288693389)
                      ·
                        rfl

theorem cell23_4399214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_4399214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399214 prefixEnd_4399214 := by exact prefixLift 4399214
  have htrace : WordTrace (prefixWord ++ tailWord_4399214) baseStart_4399214 baseEnd_4399214 := by
    simpa [prefixWord, tailWord_4399214, baseEnd_4399214] using wordTrace_append hprefix tailTrace_4399214
  have hstable : (prefixWord ++ tailWord_4399214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399214).length < 2 ^ (prefixWord ++ tailWord_4399214).sum := by decide
  have hdescent : baseEnd_4399214 < baseStart_4399214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399215 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 2, 2, 2]
def baseStart_4399215 : Nat := 118140960795 + 4399215 * 2 ^ 59
def prefixEnd_4399215 : Nat := 4983230072969 + 3 ^ 40 * 4399215 * 2
def baseEnd_4399215 : Nat := 2258911797469110784780885

theorem tailTrace_4399215 : CollatzResearch.WordTrace tailWord_4399215 prefixEnd_4399215 2258911797469110784780885 := by
  unfold tailWord_4399215
  simp only [CollatzResearch.WordTrace]
  refine ⟨160452552757402855950983099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106968368504935237300655399 160452552757402855950983099)
  ·
    refine ⟨240678829136104283926474649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160452552757402855950983099 240678829136104283926474649)
    ·
      refine ⟨180509121852078212944855987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240678829136104283926474649 180509121852078212944855987)
      ·
        refine ⟨270763682778117319417283981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180509121852078212944855987 270763682778117319417283981)
        ·
          refine ⟨101536381041793994781481493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270763682778117319417283981 101536381041793994781481493)
          ·
            refine ⟨4759517861334093505381945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101536381041793994781481493 4759517861334093505381945)
            ·
              refine ⟨3569638396000570129036459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759517861334093505381945 3569638396000570129036459)
              ·
                refine ⟨5354457594000855193554689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569638396000570129036459 5354457594000855193554689)
                ·
                  refine ⟨4015843195500641395166017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354457594000855193554689 4015843195500641395166017)
                  ·
                    refine ⟨3011882396625481046374513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4015843195500641395166017 3011882396625481046374513)
                    ·
                      refine ⟨2258911797469110784780885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3011882396625481046374513 2258911797469110784780885)
                      ·
                        rfl

theorem cell23_4399215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 2, 2].length) (baseStart_4399215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399215 prefixEnd_4399215 := by exact prefixLift 4399215
  have htrace : WordTrace (prefixWord ++ tailWord_4399215) baseStart_4399215 baseEnd_4399215 := by
    simpa [prefixWord, tailWord_4399215, baseEnd_4399215] using wordTrace_append hprefix tailTrace_4399215
  have hstable : (prefixWord ++ tailWord_4399215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399215).length < 2 ^ (prefixWord ++ tailWord_4399215).sum := by decide
  have hdescent : baseEnd_4399215 < baseStart_4399215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399217 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 4, 5]
def baseStart_4399217 : Nat := 118140960795 + 4399217 * 2 ^ 59
def prefixEnd_4399217 : Nat := 4983230072969 + 3 ^ 40 * 4399217 * 2
def baseEnd_4399217 : Nat := 752970941476806592318625

theorem tailTrace_4399217 : CollatzResearch.WordTrace tailWord_4399217 prefixEnd_4399217 752970941476806592318625 := by
  unfold tailWord_4399217
  simp only [CollatzResearch.WordTrace]
  refine ⟨160452625703395610292555905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106968417135597073528370603 160452625703395610292555905)
  ·
    refine ⟨120339469277546707719416929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160452625703395610292555905 120339469277546707719416929)
    ·
      refine ⟨90254601958160030789562697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120339469277546707719416929 90254601958160030789562697)
      ·
        refine ⟨67690951468620023092172023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90254601958160030789562697 67690951468620023092172023)
        ·
          refine ⟨101536427202930034638258035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67690951468620023092172023 101536427202930034638258035)
          ·
            refine ⟨152304640804395051957387053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101536427202930034638258035 152304640804395051957387053)
            ·
              refine ⟨57114240301648144484020145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152304640804395051957387053 57114240301648144484020145)
              ·
                refine ⟨42835680226236108363015109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57114240301648144484020145 42835680226236108363015109)
                ·
                  refine ⟨8031690042419270318065333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42835680226236108363015109 8031690042419270318065333)
                  ·
                    refine ⟨752970941476806592318625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8031690042419270318065333 752970941476806592318625)
                    ·
                      rfl

theorem cell23_4399217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_4399217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399217 prefixEnd_4399217 := by exact prefixLift 4399217
  have htrace : WordTrace (prefixWord ++ tailWord_4399217) baseStart_4399217 baseEnd_4399217 := by
    simpa [prefixWord, tailWord_4399217, baseEnd_4399217] using wordTrace_append hprefix tailTrace_4399217
  have hstable : (prefixWord ++ tailWord_4399217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399217).length < 2 ^ (prefixWord ++ tailWord_4399217).sum := by decide
  have hdescent : baseEnd_4399217 < baseStart_4399217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399255 : List Nat := [1, 1, 3, 3, 5, 1, 2, 2, 5]
def baseStart_4399255 : Nat := 118140960795 + 4399255 * 2 ^ 59
def prefixEnd_4399255 : Nat := 4983230072969 + 3 ^ 40 * 4399255 * 2
def baseEnd_4399255 : Nat := 250992481855032292031189

theorem tailTrace_4399255 : CollatzResearch.WordTrace tailWord_4399255 prefixEnd_4399255 250992481855032292031189 := by
  unfold tailWord_4399255
  simp only [CollatzResearch.WordTrace]
  refine ⟨160454011677257942782439219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106969341118171961854959479 160454011677257942782439219)
  ·
    refine ⟨240681017515886914173658829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160454011677257942782439219 240681017515886914173658829)
    ·
      refine ⟨90255381568457592815122061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240681017515886914173658829 90255381568457592815122061)
      ·
        refine ⟨33845768088171597305670773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90255381568457592815122061 33845768088171597305670773)
        ·
          refine ⟨3173040758266087247406635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33845768088171597305670773 3173040758266087247406635)
          ·
            refine ⟨4759561137399130871109953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173040758266087247406635 4759561137399130871109953)
            ·
              refine ⟨3569670853049348153332465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759561137399130871109953 3569670853049348153332465)
              ·
                refine ⟨2677253139787011114999349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3569670853049348153332465 2677253139787011114999349)
                ·
                  refine ⟨250992481855032292031189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2677253139787011114999349 250992481855032292031189)
                  ·
                    rfl

theorem cell23_4399255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 5].length) (baseStart_4399255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399255 prefixEnd_4399255 := by exact prefixLift 4399255
  have htrace : WordTrace (prefixWord ++ tailWord_4399255) baseStart_4399255 baseEnd_4399255 := by
    simpa [prefixWord, tailWord_4399255, baseEnd_4399255] using wordTrace_append hprefix tailTrace_4399255
  have hstable : (prefixWord ++ tailWord_4399255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399255).length < 2 ^ (prefixWord ++ tailWord_4399255).sum := by decide
  have hdescent : baseEnd_4399255 < baseStart_4399255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399267 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4]
def baseStart_4399267 : Nat := 118140960795 + 4399267 * 2 ^ 59
def prefixEnd_4399267 : Nat := 4983230072969 + 3 ^ 40 * 4399267 * 2
def baseEnd_4399267 : Nat := 2258938498463144581330645

theorem tailTrace_4399267 : CollatzResearch.WordTrace tailWord_4399267 prefixEnd_4399267 2258938498463144581330645 := by
  unfold tailWord_4399267
  simp only [CollatzResearch.WordTrace]
  refine ⟨160454449353214468831876055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106969632902142979221250703 160454449353214468831876055)
  ·
    refine ⟨240681674029821703247814083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160454449353214468831876055 240681674029821703247814083)
    ·
      refine ⟨361022511044732554871721125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240681674029821703247814083 361022511044732554871721125)
      ·
        refine ⟨67691720820887354038447711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 361022511044732554871721125 67691720820887354038447711)
        ·
          refine ⟨101537581231331031057671567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67691720820887354038447711 101537581231331031057671567)
          ·
            refine ⟨152306371846996546586507351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101537581231331031057671567 152306371846996546586507351)
            ·
              refine ⟨228459557770494819879761027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152306371846996546586507351 228459557770494819879761027)
              ·
                refine ⟨342689336655742229819641541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228459557770494819879761027 342689336655742229819641541)
                ·
                  refine ⟨64254250622951668091182789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342689336655742229819641541 64254250622951668091182789)
                  ·
                    refine ⟨12047671991803437767096773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64254250622951668091182789 12047671991803437767096773)
                    ·
                      refine ⟨2258938498463144581330645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12047671991803437767096773 2258938498463144581330645)
                      ·
                        rfl

theorem cell23_4399267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_4399267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399267 prefixEnd_4399267 := by exact prefixLift 4399267
  have htrace : WordTrace (prefixWord ++ tailWord_4399267) baseStart_4399267 baseEnd_4399267 := by
    simpa [prefixWord, tailWord_4399267, baseEnd_4399267] using wordTrace_append hprefix tailTrace_4399267
  have hstable : (prefixWord ++ tailWord_4399267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399267).length < 2 ^ (prefixWord ++ tailWord_4399267).sum := by decide
  have hdescent : baseEnd_4399267 < baseStart_4399267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4399285 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_4399285 : Nat := 118140960795 + 4399285 * 2 ^ 59
def prefixEnd_4399285 : Nat := 4983230072969 + 3 ^ 40 * 4399285 * 2
def baseEnd_4399285 : Nat := 752982580371641836968521

theorem tailTrace_4399285 : CollatzResearch.WordTrace tailWord_4399285 prefixEnd_4399285 752982580371641836968521 := by
  unfold tailWord_4399285
  simp only [CollatzResearch.WordTrace]
  refine ⟨160455105867149257906031309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106970070578099505270687539 160455105867149257906031309)
  ·
    refine ⟨60170664700180971714761741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160455105867149257906031309 60170664700180971714761741)
    ·
      refine ⟨22563999262567864393035653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60170664700180971714761741 22563999262567864393035653)
      ·
        refine ⟨4230749861731474573694185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22563999262567864393035653 4230749861731474573694185)
        ·
          refine ⟨3173062396298605930270639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4230749861731474573694185 3173062396298605930270639)
          ·
            refine ⟨4759593594447908895405959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173062396298605930270639 4759593594447908895405959)
            ·
              refine ⟨7139390391671863343108939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759593594447908895405959 7139390391671863343108939)
              ·
                refine ⟨10709085587507795014663409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139390391671863343108939 10709085587507795014663409)
                ·
                  refine ⟨8031814190630846260997557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10709085587507795014663409 8031814190630846260997557)
                  ·
                    refine ⟨752982580371641836968521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8031814190630846260997557 752982580371641836968521)
                    ·
                      rfl

theorem cell23_4399285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_4399285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4399285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4399285 prefixEnd_4399285 := by exact prefixLift 4399285
  have htrace : WordTrace (prefixWord ++ tailWord_4399285) baseStart_4399285 baseEnd_4399285 := by
    simpa [prefixWord, tailWord_4399285, baseEnd_4399285] using wordTrace_append hprefix tailTrace_4399285
  have hstable : (prefixWord ++ tailWord_4399285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4399285).length < 2 ^ (prefixWord ++ tailWord_4399285).sum := by decide
  have hdescent : baseEnd_4399285 < baseStart_4399285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4399285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
