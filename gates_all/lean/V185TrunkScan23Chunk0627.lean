import V185TrunkScan23Chunk0626

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3708283 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 3]
def baseStart_3708283 : Nat := 118140960795 + 3708283 * 2 ^ 59
def prefixEnd_3708283 : Nat := 4983230072969 + 3 ^ 40 * 3708283 * 2
def baseEnd_3708283 : Nat := 1904131581896820059408423

theorem tailTrace_3708283 : CollatzResearch.WordTrace tailWord_3708283 prefixEnd_3708283 1904131581896820059408423 := by
  unfold tailWord_3708283
  simp only [CollatzResearch.WordTrace]
  refine ⟨135252192424531490159985503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90168128283020993439990335 135252192424531490159985503)
  ·
    refine ⟨202878288636797235239978255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135252192424531490159985503 202878288636797235239978255)
    ·
      refine ⟨304317432955195852859967383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202878288636797235239978255 304317432955195852859967383)
      ·
        refine ⟨456476149432793779289951075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304317432955195852859967383 456476149432793779289951075)
        ·
          refine ⟨684714224149190668934926613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456476149432793779289951075 684714224149190668934926613)
          ·
            refine ⟨32095979256993312606324685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 684714224149190668934926613 32095979256993312606324685)
            ·
              refine ⟨12035992221372492227371757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32095979256993312606324685 12035992221372492227371757)
              ·
                refine ⟨4513497083014684585264409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12035992221372492227371757 4513497083014684585264409)
                ·
                  refine ⟨3385122812261013438948307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513497083014684585264409 3385122812261013438948307)
                  ·
                    refine ⟨5077684218391520158422461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3385122812261013438948307 5077684218391520158422461)
                    ·
                      refine ⟨1904131581896820059408423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5077684218391520158422461 1904131581896820059408423)
                      ·
                        rfl

theorem cell23_3708283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 3].length) (baseStart_3708283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708283 prefixEnd_3708283 := by exact prefixLift 3708283
  have htrace : WordTrace (prefixWord ++ tailWord_3708283) baseStart_3708283 baseEnd_3708283 := by
    simpa [prefixWord, tailWord_3708283, baseEnd_3708283] using wordTrace_append hprefix tailTrace_3708283
  have hstable : (prefixWord ++ tailWord_3708283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708283).length < 2 ^ (prefixWord ++ tailWord_3708283).sum := by decide
  have hdescent : baseEnd_3708283 < baseStart_3708283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708318 : List Nat := [4, 3, 1, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3708318 : Nat := 118140960795 + 3708318 * 2 ^ 59
def prefixEnd_3708318 : Nat := 4983230072969 + 3 ^ 40 * 3708318 * 2
def baseEnd_3708318 : Nat := 1904149553719727422470763

theorem tailTrace_3708318 : CollatzResearch.WordTrace tailWord_3708318 prefixEnd_3708318 1904149553719727422470763 := by
  unfold tailWord_3708318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16906683622425586392188701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90168979319603127425006405 16906683622425586392188701)
  ·
    refine ⟨6340006358409594897070763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16906683622425586392188701 6340006358409594897070763)
    ·
      refine ⟨9510009537614392345606145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6340006358409594897070763 9510009537614392345606145)
      ·
        refine ⟨7132507153210794259204609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9510009537614392345606145 7132507153210794259204609)
        ·
          refine ⟨5349380364908095694403457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7132507153210794259204609 5349380364908095694403457)
          ·
            refine ⟨4012035273681071770802593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5349380364908095694403457 4012035273681071770802593)
            ·
              refine ⟨3009026455260803828101945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012035273681071770802593 3009026455260803828101945)
              ·
                refine ⟨2256769841445602871076459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3009026455260803828101945 2256769841445602871076459)
                ·
                  refine ⟨3385154762168404306614689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256769841445602871076459 3385154762168404306614689)
                  ·
                    refine ⟨2538866071626303229961017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385154762168404306614689 2538866071626303229961017)
                    ·
                      refine ⟨1904149553719727422470763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538866071626303229961017 1904149553719727422470763)
                      ·
                        rfl

theorem cell23_3708318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3708318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708318 prefixEnd_3708318 := by exact prefixLift 3708318
  have htrace : WordTrace (prefixWord ++ tailWord_3708318) baseStart_3708318 baseEnd_3708318 := by
    simpa [prefixWord, tailWord_3708318, baseEnd_3708318] using wordTrace_append hprefix tailTrace_3708318
  have hstable : (prefixWord ++ tailWord_3708318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708318).length < 2 ^ (prefixWord ++ tailWord_3708318).sum := by decide
  have hdescent : baseEnd_3708318 < baseStart_3708318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708333 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3708333 : Nat := 118140960795 + 3708333 * 2 ^ 59
def prefixEnd_3708333 : Nat := 4983230072969 + 3 ^ 40 * 3708333 * 2
def baseEnd_3708333 : Nat := 634719085309848287927731

theorem tailTrace_3708333 : CollatzResearch.WordTrace tailWord_3708333 prefixEnd_3708333 634719085309848287927731 := by
  unfold tailWord_3708333
  simp only [CollatzResearch.WordTrace]
  refine ⟨135254016074350348699305653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90169344049566899132870435 135254016074350348699305653)
  ·
    refine ⟨12680064006970345190559905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135254016074350348699305653 12680064006970345190559905)
    ·
      refine ⟨9510048005227758892919929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12680064006970345190559905 9510048005227758892919929)
      ·
        refine ⟨7132536003920819169689947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9510048005227758892919929 7132536003920819169689947)
        ·
          refine ⟨10698804005881228754534921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7132536003920819169689947 10698804005881228754534921)
          ·
            refine ⟨8024103004410921565901191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10698804005881228754534921 8024103004410921565901191)
            ·
              refine ⟨12036154506616382348851787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8024103004410921565901191 12036154506616382348851787)
              ·
                refine ⟨18054231759924573523277681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12036154506616382348851787 18054231759924573523277681)
                ·
                  refine ⟨13540673819943430142458261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18054231759924573523277681 13540673819943430142458261)
                  ·
                    refine ⟨634719085309848287927731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13540673819943430142458261 634719085309848287927731)
                    ·
                      rfl

theorem cell23_3708333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3708333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708333 prefixEnd_3708333 := by exact prefixLift 3708333
  have htrace : WordTrace (prefixWord ++ tailWord_3708333) baseStart_3708333 baseEnd_3708333 := by
    simpa [prefixWord, tailWord_3708333, baseEnd_3708333] using wordTrace_append hprefix tailTrace_3708333
  have hstable : (prefixWord ++ tailWord_3708333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708333).length < 2 ^ (prefixWord ++ tailWord_3708333).sum := by decide
  have hdescent : baseEnd_3708333 < baseStart_3708333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708374 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_3708374 : Nat := 118140960795 + 3708374 * 2 ^ 59
def prefixEnd_3708374 : Nat := 4983230072969 + 3 ^ 40 * 3708374 * 2
def baseEnd_3708374 : Nat := 1904178308636379203370505

theorem tailTrace_3708374 : CollatzResearch.WordTrace tailWord_3708374 prefixEnd_3708374 1904178308636379203370505 := by
  unfold tailWord_3708374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453469466700113293846761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90170340978134541801032117 8453469466700113293846761)
  ·
    refine ⟨6340102100025084970385071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8453469466700113293846761 6340102100025084970385071)
    ·
      refine ⟨9510153150037627455577607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6340102100025084970385071 9510153150037627455577607)
      ·
        refine ⟨14265229725056441183366411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9510153150037627455577607 14265229725056441183366411)
        ·
          refine ⟨21397844587584661775049617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14265229725056441183366411 21397844587584661775049617)
          ·
            refine ⟨16048383440688496331287213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21397844587584661775049617 16048383440688496331287213)
            ·
              refine ⟨6018143790258186124232705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16048383440688496331287213 6018143790258186124232705)
              ·
                refine ⟨4513607842693639593174529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6018143790258186124232705 4513607842693639593174529)
                ·
                  refine ⟨3385205882020229694880897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513607842693639593174529 3385205882020229694880897)
                  ·
                    refine ⟨2538904411515172271160673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385205882020229694880897 2538904411515172271160673)
                    ·
                      refine ⟨1904178308636379203370505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538904411515172271160673 1904178308636379203370505)
                      ·
                        rfl

theorem cell23_3708374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_3708374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708374 prefixEnd_3708374 := by exact prefixLift 3708374
  have htrace : WordTrace (prefixWord ++ tailWord_3708374) baseStart_3708374 baseEnd_3708374 := by
    simpa [prefixWord, tailWord_3708374, baseEnd_3708374] using wordTrace_append hprefix tailTrace_3708374
  have hstable : (prefixWord ++ tailWord_3708374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708374).length < 2 ^ (prefixWord ++ tailWord_3708374).sum := by decide
  have hdescent : baseEnd_3708374 < baseStart_3708374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708376 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 2, 5]
def baseStart_3708376 : Nat := 118140960795 + 3708376 * 2 ^ 59
def prefixEnd_3708376 : Nat := 4983230072969 + 3 ^ 40 * 3708376 * 2
def baseEnd_3708376 : Nat := 634726445199229398515165

theorem tailTrace_3708376 : CollatzResearch.WordTrace tailWord_3708376 prefixEnd_3708376 634726445199229398515165 := by
  unfold tailWord_3708376
  simp only [CollatzResearch.WordTrace]
  refine ⟨67627792206597283521560491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90170389608796378028747321 67627792206597283521560491)
  ·
    refine ⟨101441688309895925282340737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67627792206597283521560491 101441688309895925282340737)
    ·
      refine ⟨76081266232421943961755553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101441688309895925282340737 76081266232421943961755553)
      ·
        refine ⟨57060949674316457971316665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76081266232421943961755553 57060949674316457971316665)
        ·
          refine ⟨42795712255737343478487499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57060949674316457971316665 42795712255737343478487499)
          ·
            refine ⟨64193568383606015217731249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42795712255737343478487499 64193568383606015217731249)
            ·
              refine ⟨48145176287704511413298437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64193568383606015217731249 48145176287704511413298437)
              ·
                refine ⟨9027220553944595889993457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48145176287704511413298437 9027220553944595889993457)
                ·
                  refine ⟨6770415415458446917495093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9027220553944595889993457 6770415415458446917495093)
                  ·
                    refine ⟨634726445199229398515165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6770415415458446917495093 634726445199229398515165)
                    ·
                      rfl

theorem cell23_3708376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_3708376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708376 prefixEnd_3708376 := by exact prefixLift 3708376
  have htrace : WordTrace (prefixWord ++ tailWord_3708376) baseStart_3708376 baseEnd_3708376 := by
    simpa [prefixWord, tailWord_3708376, baseEnd_3708376] using wordTrace_append hprefix tailTrace_3708376
  have hstable : (prefixWord ++ tailWord_3708376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708376).length < 2 ^ (prefixWord ++ tailWord_3708376).sum := by decide
  have hdescent : baseEnd_3708376 < baseStart_3708376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708396 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_3708396 : Nat := 118140960795 + 3708396 * 2 ^ 59
def prefixEnd_3708396 : Nat := 4983230072969 + 3 ^ 40 * 3708396 * 2
def baseEnd_3708396 : Nat := 1904189605210778117295403

theorem tailTrace_3708396 : CollatzResearch.WordTrace tailWord_3708396 prefixEnd_3708396 1904189605210778117295403 := by
  unfold tailWord_3708396
  simp only [CollatzResearch.WordTrace]
  refine ⟨67628156936561055229424521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90170875915414740305899361 67628156936561055229424521)
  ·
    refine ⟨50721117702420791422068391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67628156936561055229424521 50721117702420791422068391)
    ·
      refine ⟨76081676553631187133102587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50721117702420791422068391 76081676553631187133102587)
      ·
        refine ⟨114122514830446780699653881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76081676553631187133102587 114122514830446780699653881)
        ·
          refine ⟨85591886122835085524740411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114122514830446780699653881 85591886122835085524740411)
          ·
            refine ⟨128387829184252628287110617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85591886122835085524740411 128387829184252628287110617)
            ·
              refine ⟨96290871888189471215332963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128387829184252628287110617 96290871888189471215332963)
              ·
                refine ⟨144436307832284206822999445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96290871888189471215332963 144436307832284206822999445)
                ·
                  refine ⟨6770451929638322194828099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144436307832284206822999445 6770451929638322194828099)
                  ·
                    refine ⟨10155677894457483292242149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6770451929638322194828099 10155677894457483292242149)
                    ·
                      refine ⟨1904189605210778117295403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10155677894457483292242149 1904189605210778117295403)
                      ·
                        rfl

theorem cell23_3708396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_3708396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708396 prefixEnd_3708396 := by exact prefixLift 3708396
  have htrace : WordTrace (prefixWord ++ tailWord_3708396) baseStart_3708396 baseEnd_3708396 := by
    simpa [prefixWord, tailWord_3708396, baseEnd_3708396] using wordTrace_append hprefix tailTrace_3708396
  have hstable : (prefixWord ++ tailWord_3708396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708396).length < 2 ^ (prefixWord ++ tailWord_3708396).sum := by decide
  have hdescent : baseEnd_3708396 < baseStart_3708396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708414 : List Nat := [4, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_3708414 : Nat := 118140960795 + 3708414 * 2 ^ 59
def prefixEnd_3708414 : Nat := 4983230072969 + 3 ^ 40 * 3708414 * 2
def baseEnd_3708414 : Nat := 211577649762506560763369

theorem tailTrace_3708414 : CollatzResearch.WordTrace tailWord_3708414 prefixEnd_3708414 211577649762506560763369 := by
  unfold tailWord_3708414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16907121298382112441625537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90171313591371266355336197 16907121298382112441625537)
  ·
    refine ⟨12680340973786584331219153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16907121298382112441625537 12680340973786584331219153)
    ·
      refine ⟨9510255730339938248414365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12680340973786584331219153 9510255730339938248414365)
      ·
        refine ⟨3566345898877476843155387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9510255730339938248414365 3566345898877476843155387)
        ·
          refine ⟨5349518848316215264733081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566345898877476843155387 5349518848316215264733081)
          ·
            refine ⟨4012139136237161448549811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5349518848316215264733081 4012139136237161448549811)
            ·
              refine ⟨6018208704355742172824717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012139136237161448549811 6018208704355742172824717)
              ·
                refine ⟨2256828264133403314809269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6018208704355742172824717 2256828264133403314809269)
                ·
                  refine ⟨211577649762506560763369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2256828264133403314809269 211577649762506560763369)
                  ·
                    rfl

theorem cell23_3708414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_3708414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708414 prefixEnd_3708414 := by exact prefixLift 3708414
  have htrace : WordTrace (prefixWord ++ tailWord_3708414) baseStart_3708414 baseEnd_3708414 := by
    simpa [prefixWord, tailWord_3708414, baseEnd_3708414] using wordTrace_append hprefix tailTrace_3708414
  have hstable : (prefixWord ++ tailWord_3708414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708414).length < 2 ^ (prefixWord ++ tailWord_3708414).sum := by decide
  have hdescent : baseEnd_3708414 < baseStart_3708414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708430 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3708430 : Nat := 118140960795 + 3708430 * 2 ^ 59
def prefixEnd_3708430 : Nat := 4983230072969 + 3 ^ 40 * 3708430 * 2
def baseEnd_3708430 : Nat := 1904207063553030984270247

theorem tailTrace_3708430 : CollatzResearch.WordTrace tailWord_3708430 prefixEnd_3708430 1904207063553030984270247 := by
  unfold tailWord_3708430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16907194244374866783198343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90171702636665956177057829 16907194244374866783198343)
  ·
    refine ⟨25360791366562300174797515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16907194244374866783198343 25360791366562300174797515)
    ·
      refine ⟨38041187049843450262196273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25360791366562300174797515 38041187049843450262196273)
      ·
        refine ⟨28530890287382587696647205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38041187049843450262196273 28530890287382587696647205)
        ·
          refine ⟨5349541928884235193121351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28530890287382587696647205 5349541928884235193121351)
          ·
            refine ⟨8024312893326352789682027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5349541928884235193121351 8024312893326352789682027)
            ·
              refine ⟨12036469339989529184523041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8024312893326352789682027 12036469339989529184523041)
              ·
                refine ⟨9027352004992146888392281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12036469339989529184523041 9027352004992146888392281)
                ·
                  refine ⟨6770514003744110166294211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9027352004992146888392281 6770514003744110166294211)
                  ·
                    refine ⟨10155771005616165249441317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6770514003744110166294211 10155771005616165249441317)
                    ·
                      refine ⟨1904207063553030984270247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10155771005616165249441317 1904207063553030984270247)
                      ·
                        rfl

theorem cell23_3708430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3708430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708430 prefixEnd_3708430 := by exact prefixLift 3708430
  have htrace : WordTrace (prefixWord ++ tailWord_3708430) baseStart_3708430 baseEnd_3708430 := by
    simpa [prefixWord, tailWord_3708430, baseEnd_3708430] using wordTrace_append hprefix tailTrace_3708430
  have hstable : (prefixWord ++ tailWord_3708430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708430).length < 2 ^ (prefixWord ++ tailWord_3708430).sum := by decide
  have hdescent : baseEnd_3708430 < baseStart_3708430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708433 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_3708433 : Nat := 118140960795 + 3708433 * 2 ^ 59
def prefixEnd_3708433 : Nat := 4983230072969 + 3 ^ 40 * 3708433 * 2
def baseEnd_3708433 : Nat := 1904208603994994472532733

theorem tailTrace_3708433 : CollatzResearch.WordTrace tailWord_3708433 prefixEnd_3708433 1904208603994994472532733 := by
  unfold tailWord_3708433
  simp only [CollatzResearch.WordTrace]
  refine ⟨135257663373988065777945953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90171775582658710518630635 135257663373988065777945953)
  ·
    refine ⟨101443247530491049333459465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135257663373988065777945953 101443247530491049333459465)
    ·
      refine ⟨76082435647868287000094599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101443247530491049333459465 76082435647868287000094599)
      ·
        refine ⟨114123653471802430500141899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76082435647868287000094599 114123653471802430500141899)
        ·
          refine ⟨171185480207703645750212849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114123653471802430500141899 171185480207703645750212849)
          ·
            refine ⟨128389110155777734312659637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171185480207703645750212849 128389110155777734312659637)
            ·
              refine ⟨12036479077104162591811841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128389110155777734312659637 12036479077104162591811841)
              ·
                refine ⟨9027359307828121943858881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12036479077104162591811841 9027359307828121943858881)
                ·
                  refine ⟨6770519480871091457894161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9027359307828121943858881 6770519480871091457894161)
                  ·
                    refine ⟨5077889610653318593420621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6770519480871091457894161 5077889610653318593420621)
                    ·
                      refine ⟨1904208603994994472532733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5077889610653318593420621 1904208603994994472532733)
                      ·
                        rfl

theorem cell23_3708433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_3708433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708433 prefixEnd_3708433 := by exact prefixLift 3708433
  have htrace : WordTrace (prefixWord ++ tailWord_3708433) baseStart_3708433 baseEnd_3708433 := by
    simpa [prefixWord, tailWord_3708433, baseEnd_3708433] using wordTrace_append hprefix tailTrace_3708433
  have hstable : (prefixWord ++ tailWord_3708433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708433).length < 2 ^ (prefixWord ++ tailWord_3708433).sum := by decide
  have hdescent : baseEnd_3708433 < baseStart_3708433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708490 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_3708490 : Nat := 118140960795 + 3708490 * 2 ^ 59
def prefixEnd_3708490 : Nat := 4983230072969 + 3 ^ 40 * 3708490 * 2
def baseEnd_3708490 : Nat := 1904237872392300749519971

theorem tailTrace_3708490 : CollatzResearch.WordTrace tailWord_3708490 prefixEnd_3708490 1904237872392300749519971 := by
  unfold tailWord_3708490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33814935583695391128192731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90173161556521043008513949 33814935583695391128192731)
  ·
    refine ⟨50722403375543086692289097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33814935583695391128192731 50722403375543086692289097)
    ·
      refine ⟨38041802531657315019216823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50722403375543086692289097 38041802531657315019216823)
      ·
        refine ⟨57062703797485972528825235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38041802531657315019216823 57062703797485972528825235)
        ·
          refine ⟨85594055696228958793237853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57062703797485972528825235 85594055696228958793237853)
          ·
            refine ⟨32097770886085859547464195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85594055696228958793237853 32097770886085859547464195)
            ·
              refine ⟨48146656329128789321196293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32097770886085859547464195 48146656329128789321196293)
              ·
                refine ⟨9027498061711647997724305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48146656329128789321196293 9027498061711647997724305)
                ·
                  refine ⟨6770623546283735998293229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9027498061711647997724305 6770623546283735998293229)
                  ·
                    refine ⟨2538983829856400999359961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6770623546283735998293229 2538983829856400999359961)
                    ·
                      refine ⟨1904237872392300749519971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2538983829856400999359961 1904237872392300749519971)
                      ·
                        rfl

theorem cell23_3708490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_3708490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708490 prefixEnd_3708490 := by exact prefixLift 3708490
  have htrace : WordTrace (prefixWord ++ tailWord_3708490) baseStart_3708490 baseEnd_3708490 := by
    simpa [prefixWord, tailWord_3708490, baseEnd_3708490] using wordTrace_append hprefix tailTrace_3708490
  have hstable : (prefixWord ++ tailWord_3708490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708490).length < 2 ^ (prefixWord ++ tailWord_3708490).sum := by decide
  have hdescent : baseEnd_3708490 < baseStart_3708490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708496 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 3, 6]
def baseStart_3708496 : Nat := 118140960795 + 3708496 * 2 ^ 59
def prefixEnd_3708496 : Nat := 4983230072969 + 3 ^ 40 * 3708496 * 2
def baseEnd_3708496 : Nat := 634746984425409242014981

theorem tailTrace_3708496 : CollatzResearch.WordTrace tailWord_3708496 prefixEnd_3708496 634746984425409242014981 := by
  unfold tailWord_3708496
  simp only [CollatzResearch.WordTrace]
  refine ⟨67629980586379913768744671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90173307448506551691659561 67629980586379913768744671)
  ·
    refine ⟨101444970879569870653117007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67629980586379913768744671 101444970879569870653117007)
    ·
      refine ⟨152167456319354805979675511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101444970879569870653117007 152167456319354805979675511)
      ·
        refine ⟨228251184479032208969513267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152167456319354805979675511 228251184479032208969513267)
        ·
          refine ⟨342376776718548313454269901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228251184479032208969513267 342376776718548313454269901)
          ·
            refine ⟨128391291269455617545351213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342376776718548313454269901 128391291269455617545351213)
            ·
              refine ⟨48146734226045856579506705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128391291269455617545351213 48146734226045856579506705)
              ·
                refine ⟨36110050669534392434630029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48146734226045856579506705 36110050669534392434630029)
                ·
                  refine ⟨13541269001075397162986261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36110050669534392434630029 13541269001075397162986261)
                  ·
                    refine ⟨634746984425409242014981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13541269001075397162986261 634746984425409242014981)
                    ·
                      rfl

theorem cell23_3708496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_3708496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708496 prefixEnd_3708496 := by exact prefixLift 3708496
  have htrace : WordTrace (prefixWord ++ tailWord_3708496) baseStart_3708496 baseEnd_3708496 := by
    simpa [prefixWord, tailWord_3708496, baseEnd_3708496] using wordTrace_append hprefix tailTrace_3708496
  have hstable : (prefixWord ++ tailWord_3708496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708496).length < 2 ^ (prefixWord ++ tailWord_3708496).sum := by decide
  have hdescent : baseEnd_3708496 < baseStart_3708496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708497 : List Nat := [1, 2, 2, 1, 3, 2, 3, 4, 1, 1, 3]
def baseStart_3708497 : Nat := 118140960795 + 3708497 * 2 ^ 59
def prefixEnd_3708497 : Nat := 4983230072969 + 3 ^ 40 * 3708497 * 2
def baseEnd_3708497 : Nat := 1904241466756882222132439

theorem tailTrace_3708497 : CollatzResearch.WordTrace tailWord_3708497 prefixEnd_3708497 1904241466756882222132439 := by
  unfold tailWord_3708497
  simp only [CollatzResearch.WordTrace]
  refine ⟨135259997645756204708275745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90173331763837469805517163 135259997645756204708275745)
  ·
    refine ⟨101444998234317153531206809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135259997645756204708275745 101444998234317153531206809)
    ·
      refine ⟨76083748675737865148405107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101444998234317153531206809 76083748675737865148405107)
      ·
        refine ⟨114125623013606797722607661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76083748675737865148405107 114125623013606797722607661)
        ·
          refine ⟨42797108630102549145977873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114125623013606797722607661 42797108630102549145977873)
          ·
            refine ⟨32097831472576911859483405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42797108630102549145977873 32097831472576911859483405)
            ·
              refine ⟨12036686802216341947306277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32097831472576911859483405 12036686802216341947306277)
              ·
                refine ⟨2256878775415564115119927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12036686802216341947306277 2256878775415564115119927)
                ·
                  refine ⟨3385318163123346172679891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256878775415564115119927 3385318163123346172679891)
                  ·
                    refine ⟨5077977244685019259019837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3385318163123346172679891 5077977244685019259019837)
                    ·
                      refine ⟨1904241466756882222132439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5077977244685019259019837 1904241466756882222132439)
                      ·
                        rfl

theorem cell23_3708497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_3708497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708497 prefixEnd_3708497 := by exact prefixLift 3708497
  have htrace : WordTrace (prefixWord ++ tailWord_3708497) baseStart_3708497 baseEnd_3708497 := by
    simpa [prefixWord, tailWord_3708497, baseEnd_3708497] using wordTrace_append hprefix tailTrace_3708497
  have hstable : (prefixWord ++ tailWord_3708497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708497).length < 2 ^ (prefixWord ++ tailWord_3708497).sum := by decide
  have hdescent : baseEnd_3708497 < baseStart_3708497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708503 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_3708503 : Nat := 118140960795 + 3708503 * 2 ^ 59
def prefixEnd_3708503 : Nat := 4983230072969 + 3 ^ 40 * 3708503 * 2
def baseEnd_3708503 : Nat := 1904244547640809198657411

theorem tailTrace_3708503 : CollatzResearch.WordTrace tailWord_3708503 prefixEnd_3708503 1904244547640809198657411 := by
  unfold tailWord_3708503
  simp only [CollatzResearch.WordTrace]
  refine ⟨135260216483734467732994163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90173477655822978488662775 135260216483734467732994163)
  ·
    refine ⟨202890324725601701599491245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135260216483734467732994163 202890324725601701599491245)
    ·
      refine ⟨76083871772100638099809217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202890324725601701599491245 76083871772100638099809217)
      ·
        refine ⟨57062903829075478574856913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76083871772100638099809217 57062903829075478574856913)
        ·
          refine ⟨42797177871806608931142685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57062903829075478574856913 42797177871806608931142685)
          ·
            refine ⟨16048941701927478349178507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42797177871806608931142685 16048941701927478349178507)
            ·
              refine ⟨24073412552891217523767761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16048941701927478349178507 24073412552891217523767761)
              ·
                refine ⟨18055059414668413142825821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24073412552891217523767761 18055059414668413142825821)
                ·
                  refine ⟨6770647280500654928559683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18055059414668413142825821 6770647280500654928559683)
                  ·
                    refine ⟨10155970920750982392839525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6770647280500654928559683 10155970920750982392839525)
                    ·
                      refine ⟨1904244547640809198657411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10155970920750982392839525 1904244547640809198657411)
                      ·
                        rfl

theorem cell23_3708503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_3708503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708503 prefixEnd_3708503 := by exact prefixLift 3708503
  have htrace : WordTrace (prefixWord ++ tailWord_3708503) baseStart_3708503 baseEnd_3708503 := by
    simpa [prefixWord, tailWord_3708503, baseEnd_3708503] using wordTrace_append hprefix tailTrace_3708503
  have hstable : (prefixWord ++ tailWord_3708503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708503).length < 2 ^ (prefixWord ++ tailWord_3708503).sum := by decide
  have hdescent : baseEnd_3708503 < baseStart_3708503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708513 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3708513 : Nat := 118140960795 + 3708513 * 2 ^ 59
def prefixEnd_3708513 : Nat := 4983230072969 + 3 ^ 40 * 3708513 * 2
def baseEnd_3708513 : Nat := 634749894149118053177455

theorem tailTrace_3708513 : CollatzResearch.WordTrace tailWord_3708513 prefixEnd_3708513 634749894149118053177455 := by
  unfold tailWord_3708513
  simp only [CollatzResearch.WordTrace]
  refine ⟨135260581213698239440858193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90173720809132159627238795 135260581213698239440858193)
  ·
    refine ⟨101445435910273679580643645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135260581213698239440858193 101445435910273679580643645)
    ·
      refine ⟨38042038466352629842741367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101445435910273679580643645 38042038466352629842741367)
      ·
        refine ⟨57063057699528944764112051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38042038466352629842741367 57063057699528944764112051)
        ·
          refine ⟨85594586549293417146168077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57063057699528944764112051 85594586549293417146168077)
          ·
            refine ⟨32097969955985031429813029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85594586549293417146168077 32097969955985031429813029)
            ·
              refine ⟨6018369366747193393089943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32097969955985031429813029 6018369366747193393089943)
              ·
                refine ⟨9027554050120790089634915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6018369366747193393089943 9027554050120790089634915)
                ·
                  refine ⟨13541331075181185134452373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9027554050120790089634915 13541331075181185134452373)
                  ·
                    refine ⟨634749894149118053177455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13541331075181185134452373 634749894149118053177455)
                    ·
                      rfl

theorem cell23_3708513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3708513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708513 prefixEnd_3708513 := by exact prefixLift 3708513
  have htrace : WordTrace (prefixWord ++ tailWord_3708513) baseStart_3708513 baseEnd_3708513 := by
    simpa [prefixWord, tailWord_3708513, baseEnd_3708513] using wordTrace_append hprefix tailTrace_3708513
  have hstable : (prefixWord ++ tailWord_3708513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708513).length < 2 ^ (prefixWord ++ tailWord_3708513).sum := by decide
  have hdescent : baseEnd_3708513 < baseStart_3708513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708520 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3708520 : Nat := 118140960795 + 3708520 * 2 ^ 59
def prefixEnd_3708520 : Nat := 4983230072969 + 3 ^ 40 * 3708520 * 2
def baseEnd_3708520 : Nat := 1904253276811935632144833

theorem tailTrace_3708520 : CollatzResearch.WordTrace tailWord_3708520 prefixEnd_3708520 1904253276811935632144833 := by
  unfold tailWord_3708520
  simp only [CollatzResearch.WordTrace]
  refine ⟨67630418262336439818181507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90173891016448586424242009 67630418262336439818181507)
  ·
    refine ⟨101445627393504659727272261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67630418262336439818181507 101445627393504659727272261)
    ·
      refine ⟨19021055136282123698863549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101445627393504659727272261 19021055136282123698863549)
      ·
        refine ⟨7132895676105796387073831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19021055136282123698863549 7132895676105796387073831)
        ·
          refine ⟨10699343514158694580610747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7132895676105796387073831 10699343514158694580610747)
          ·
            refine ⟨16049015271238041870916121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10699343514158694580610747 16049015271238041870916121)
            ·
              refine ⟨12036761453428531403187091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16049015271238041870916121 12036761453428531403187091)
              ·
                refine ⟨18055142180142797104780637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12036761453428531403187091 18055142180142797104780637)
                ·
                  refine ⟨6770678317553548914292739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18055142180142797104780637 6770678317553548914292739)
                  ·
                    refine ⟨10156017476330323371439109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6770678317553548914292739 10156017476330323371439109)
                    ·
                      refine ⟨1904253276811935632144833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10156017476330323371439109 1904253276811935632144833)
                      ·
                        rfl

theorem cell23_3708520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3708520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708520 prefixEnd_3708520 := by exact prefixLift 3708520
  have htrace : WordTrace (prefixWord ++ tailWord_3708520) baseStart_3708520 baseEnd_3708520 := by
    simpa [prefixWord, tailWord_3708520, baseEnd_3708520] using wordTrace_append hprefix tailTrace_3708520
  have hstable : (prefixWord ++ tailWord_3708520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708520).length < 2 ^ (prefixWord ++ tailWord_3708520).sum := by decide
  have hdescent : baseEnd_3708520 < baseStart_3708520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708534 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_3708534 : Nat := 118140960795 + 3708534 * 2 ^ 59
def prefixEnd_3708534 : Nat := 4983230072969 + 3 ^ 40 * 3708534 * 2
def baseEnd_3708534 : Nat := 634753488513699525789923

theorem tailTrace_3708534 : CollatzResearch.WordTrace tailWord_3708534 prefixEnd_3708534 634753488513699525789923 := by
  unfold tailWord_3708534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453834196663885001710791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90174231431081440018248437 8453834196663885001710791)
  ·
    refine ⟨12680751294995827502566187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8453834196663885001710791 12680751294995827502566187)
    ·
      refine ⟨19021126942493741253849281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12680751294995827502566187 19021126942493741253849281)
      ·
        refine ⟨14265845206870305940386961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19021126942493741253849281 14265845206870305940386961)
        ·
          refine ⟨10699383905152729455290221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14265845206870305940386961 10699383905152729455290221)
          ·
            refine ⟨4012268964432273545733833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10699383905152729455290221 4012268964432273545733833)
            ·
              refine ⟨3009201723324205159300375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012268964432273545733833 3009201723324205159300375)
              ·
                refine ⟨4513802584986307738950563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009201723324205159300375 4513802584986307738950563)
                ·
                  refine ⟨6770703877479461608425845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513802584986307738950563 6770703877479461608425845)
                  ·
                    refine ⟨634753488513699525789923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6770703877479461608425845 634753488513699525789923)
                    ·
                      rfl

theorem cell23_3708534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_3708534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708534 prefixEnd_3708534 := by exact prefixLift 3708534
  have htrace : WordTrace (prefixWord ++ tailWord_3708534) baseStart_3708534 baseEnd_3708534 := by
    simpa [prefixWord, tailWord_3708534, baseEnd_3708534] using wordTrace_append hprefix tailTrace_3708534
  have hstable : (prefixWord ++ tailWord_3708534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708534).length < 2 ^ (prefixWord ++ tailWord_3708534).sum := by decide
  have hdescent : baseEnd_3708534 < baseStart_3708534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708553 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_3708553 : Nat := 118140960795 + 3708553 * 2 ^ 59
def prefixEnd_3708553 : Nat := 4983230072969 + 3 ^ 40 * 3708553 * 2
def baseEnd_3708553 : Nat := 1904270221673534003032181

theorem tailTrace_3708553 : CollatzResearch.WordTrace tailWord_3708553 prefixEnd_3708553 1904270221673534003032181 := by
  unfold tailWord_3708553
  simp only [CollatzResearch.WordTrace]
  refine ⟨135262040133553326272314313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90174693422368884181542875 135262040133553326272314313)
  ·
    refine ⟨101446530100164994704235735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135262040133553326272314313 101446530100164994704235735)
    ·
      refine ⟨152169795150247492056353603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101446530100164994704235735 152169795150247492056353603)
      ·
        refine ⟨228254692725371238084530405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152169795150247492056353603 228254692725371238084530405)
        ·
          refine ⟨42797754886007107140849451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228254692725371238084530405 42797754886007107140849451)
          ·
            refine ⟨64196632329010660711274177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42797754886007107140849451 64196632329010660711274177)
            ·
              refine ⟨48147474246757995533455633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64196632329010660711274177 48147474246757995533455633)
              ·
                refine ⟨36110605685068496650091725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48147474246757995533455633 36110605685068496650091725)
                ·
                  refine ⟨13541477131900686243784397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36110605685068496650091725 13541477131900686243784397)
                  ·
                    refine ⟨5078053924462757341419149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13541477131900686243784397 5078053924462757341419149)
                    ·
                      refine ⟨1904270221673534003032181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5078053924462757341419149 1904270221673534003032181)
                      ·
                        rfl

theorem cell23_3708553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_3708553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708553 prefixEnd_3708553 := by exact prefixLift 3708553
  have htrace : WordTrace (prefixWord ++ tailWord_3708553) baseStart_3708553 baseEnd_3708553 := by
    simpa [prefixWord, tailWord_3708553, baseEnd_3708553] using wordTrace_append hprefix tailTrace_3708553
  have hstable : (prefixWord ++ tailWord_3708553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708553).length < 2 ^ (prefixWord ++ tailWord_3708553).sum := by decide
  have hdescent : baseEnd_3708553 < baseStart_3708553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708554 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_3708554 : Nat := 118140960795 + 3708554 * 2 ^ 59
def prefixEnd_3708554 : Nat := 4983230072969 + 3 ^ 40 * 3708554 * 2
def baseEnd_3708554 : Nat := 1904270735154188499119677

theorem tailTrace_3708554 : CollatzResearch.WordTrace tailWord_3708554 prefixEnd_3708554 1904270735154188499119677 := by
  unfold tailWord_3708554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815519151637425860775179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90174717737699802295400477 33815519151637425860775179)
  ·
    refine ⟨50723278727456138791162769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33815519151637425860775179 50723278727456138791162769)
    ·
      refine ⟨38042459045592104093372077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50723278727456138791162769 38042459045592104093372077)
      ·
        refine ⟨14265922142097039035014529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38042459045592104093372077 14265922142097039035014529)
        ·
          refine ⟨10699441606572779276260897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14265922142097039035014529 10699441606572779276260897)
          ·
            refine ⟨8024581204929584457195673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10699441606572779276260897 8024581204929584457195673)
            ·
              refine ⟨6018435903697188342896755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8024581204929584457195673 6018435903697188342896755)
              ·
                refine ⟨9027653855545782514345133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6018435903697188342896755 9027653855545782514345133)
                ·
                  refine ⟨3385370195829668442879425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9027653855545782514345133 3385370195829668442879425)
                  ·
                    refine ⟨2539027646872251332159569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385370195829668442879425 2539027646872251332159569)
                    ·
                      refine ⟨1904270735154188499119677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2539027646872251332159569 1904270735154188499119677)
                      ·
                        rfl

theorem cell23_3708554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_3708554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708554 prefixEnd_3708554 := by exact prefixLift 3708554
  have htrace : WordTrace (prefixWord ++ tailWord_3708554) baseStart_3708554 baseEnd_3708554 := by
    simpa [prefixWord, tailWord_3708554, baseEnd_3708554] using wordTrace_append hprefix tailTrace_3708554
  have hstable : (prefixWord ++ tailWord_3708554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708554).length < 2 ^ (prefixWord ++ tailWord_3708554).sum := by decide
  have hdescent : baseEnd_3708554 < baseStart_3708554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708564 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3708564 : Nat := 118140960795 + 3708564 * 2 ^ 59
def prefixEnd_3708564 : Nat := 4983230072969 + 3 ^ 40 * 3708564 * 2
def baseEnd_3708564 : Nat := 634758623320244486664877

theorem tailTrace_3708564 : CollatzResearch.WordTrace tailWord_3708564 prefixEnd_3708564 634758623320244486664877 := by
  unfold tailWord_3708564
  simp only [CollatzResearch.WordTrace]
  refine ⟨67631220668256737575482373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90174960891008983433976497 67631220668256737575482373)
  ·
    refine ⟨12680853875298138295402945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67631220668256737575482373 12680853875298138295402945)
    ·
      refine ⟨9510640406473603721552209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12680853875298138295402945 9510640406473603721552209)
      ·
        refine ⟨7132980304855202791164157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9510640406473603721552209 7132980304855202791164157)
        ·
          refine ⟨2674867614320701046686559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7132980304855202791164157 2674867614320701046686559)
          ·
            refine ⟨4012301421481051570029839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674867614320701046686559 4012301421481051570029839)
            ·
              refine ⟨6018452132221577355044759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012301421481051570029839 6018452132221577355044759)
              ·
                refine ⟨9027678198332366032567139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6018452132221577355044759 9027678198332366032567139)
                ·
                  refine ⟨13541517297498549048850709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9027678198332366032567139 13541517297498549048850709)
                  ·
                    refine ⟨634758623320244486664877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13541517297498549048850709 634758623320244486664877)
                    ·
                      rfl

theorem cell23_3708564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3708564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708564 prefixEnd_3708564 := by exact prefixLift 3708564
  have htrace : WordTrace (prefixWord ++ tailWord_3708564) baseStart_3708564 baseEnd_3708564 := by
    simpa [prefixWord, tailWord_3708564, baseEnd_3708564] using wordTrace_append hprefix tailTrace_3708564
  have hstable : (prefixWord ++ tailWord_3708564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708564).length < 2 ^ (prefixWord ++ tailWord_3708564).sum := by decide
  have hdescent : baseEnd_3708564 < baseStart_3708564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708574 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3708574 : Nat := 118140960795 + 3708574 * 2 ^ 59
def prefixEnd_3708574 : Nat := 4983230072969 + 3 ^ 40 * 3708574 * 2
def baseEnd_3708574 : Nat := 1904281004767278420869585

theorem tailTrace_3708574 : CollatzResearch.WordTrace tailWord_3708574 prefixEnd_3708574 1904281004767278420869585 := by
  unfold tailWord_3708574
  simp only [CollatzResearch.WordTrace]
  refine ⟨16907850758309655857353597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90175204044318164572552517 16907850758309655857353597)
  ·
    refine ⟨6340444034366120946507599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16907850758309655857353597 6340444034366120946507599)
    ·
      refine ⟨9510666051549181419761399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6340444034366120946507599 9510666051549181419761399)
      ·
        refine ⟨14265999077323772129642099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9510666051549181419761399 14265999077323772129642099)
        ·
          refine ⟨21398998615985658194463149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14265999077323772129642099 21398998615985658194463149)
          ·
            refine ⟨8024624480994621822923681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21398998615985658194463149 8024624480994621822923681)
            ·
              refine ⟨6018468360745966367192761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8024624480994621822923681 6018468360745966367192761)
              ·
                refine ⟨4513851270559474775394571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6018468360745966367192761 4513851270559474775394571)
                ·
                  refine ⟨6770776905839212163091857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513851270559474775394571 6770776905839212163091857)
                  ·
                    refine ⟨5078082679379409122318893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6770776905839212163091857 5078082679379409122318893)
                    ·
                      refine ⟨1904281004767278420869585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5078082679379409122318893 1904281004767278420869585)
                      ·
                        rfl

theorem cell23_3708574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3708574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708574 prefixEnd_3708574 := by exact prefixLift 3708574
  have htrace : WordTrace (prefixWord ++ tailWord_3708574) baseStart_3708574 baseEnd_3708574 := by
    simpa [prefixWord, tailWord_3708574, baseEnd_3708574] using wordTrace_append hprefix tailTrace_3708574
  have hstable : (prefixWord ++ tailWord_3708574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708574).length < 2 ^ (prefixWord ++ tailWord_3708574).sum := by decide
  have hdescent : baseEnd_3708574 < baseStart_3708574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708613 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_3708613 : Nat := 118140960795 + 3708613 * 2 ^ 59
def prefixEnd_3708613 : Nat := 4983230072969 + 3 ^ 40 * 3708613 * 2
def baseEnd_3708613 : Nat := 1904301030512803768281905

theorem tailTrace_3708613 : CollatzResearch.WordTrace tailWord_3708613 prefixEnd_3708613 1904301030512803768281905 := by
  unfold tailWord_3708613
  simp only [CollatzResearch.WordTrace]
  refine ⟨135264228513335956519498493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90176152342223971012998995 135264228513335956519498493)
  ·
    refine ⟨50724085692500983694811935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135264228513335956519498493 50724085692500983694811935)
    ·
      refine ⟨76086128538751475542217903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50724085692500983694811935 76086128538751475542217903)
      ·
        refine ⟨114129192808127213313326855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76086128538751475542217903 114129192808127213313326855)
        ·
          refine ⟨171193789212190819969990283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114129192808127213313326855 171193789212190819969990283)
          ·
            refine ⟨256790683818286229954985425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171193789212190819969990283 256790683818286229954985425)
            ·
              refine ⟨192593012863714672466239069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256790683818286229954985425 192593012863714672466239069)
              ·
                refine ⟨72222379823893002174839651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192593012863714672466239069 72222379823893002174839651)
                ·
                  refine ⟨108333569735839503262259477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72222379823893002174839651 108333569735839503262259477)
                  ·
                    refine ⟨5078136081367476715418413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108333569735839503262259477 5078136081367476715418413)
                    ·
                      refine ⟨1904301030512803768281905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5078136081367476715418413 1904301030512803768281905)
                      ·
                        rfl

theorem cell23_3708613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_3708613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708613 prefixEnd_3708613 := by exact prefixLift 3708613
  have htrace : WordTrace (prefixWord ++ tailWord_3708613) baseStart_3708613 baseEnd_3708613 := by
    simpa [prefixWord, tailWord_3708613, baseEnd_3708613] using wordTrace_append hprefix tailTrace_3708613
  have hstable : (prefixWord ++ tailWord_3708613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708613).length < 2 ^ (prefixWord ++ tailWord_3708613).sum := by decide
  have hdescent : baseEnd_3708613 < baseStart_3708613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708621 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3708621 : Nat := 118140960795 + 3708621 * 2 ^ 59
def prefixEnd_3708621 : Nat := 4983230072969 + 3 ^ 40 * 3708621 * 2
def baseEnd_3708621 : Nat := 1904305138358039736981869

theorem tailTrace_3708621 : CollatzResearch.WordTrace tailWord_3708621 prefixEnd_3708621 1904305138358039736981869 := by
  unfold tailWord_3708621
  simp only [CollatzResearch.WordTrace]
  refine ⟨135264520297306973885789717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90176346864871315923859811 135264520297306973885789717)
  ·
    refine ⟨6340524388936264400896393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135264520297306973885789717 6340524388936264400896393)
    ·
      refine ⟨4755393291702198300672295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6340524388936264400896393 4755393291702198300672295)
      ·
        refine ⟨7133089937553297451008443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4755393291702198300672295 7133089937553297451008443)
        ·
          refine ⟨10699634906329946176512665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7133089937553297451008443 10699634906329946176512665)
          ·
            refine ⟨8024726179747459632384499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10699634906329946176512665 8024726179747459632384499)
            ·
              refine ⟨12037089269621189448576749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8024726179747459632384499 12037089269621189448576749)
              ·
                refine ⟨4513908476107946043216281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12037089269621189448576749 4513908476107946043216281)
                ·
                  refine ⟨3385431357080959532412211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513908476107946043216281 3385431357080959532412211)
                  ·
                    refine ⟨5078147035621439298618317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3385431357080959532412211 5078147035621439298618317)
                    ·
                      refine ⟨1904305138358039736981869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5078147035621439298618317 1904305138358039736981869)
                      ·
                        rfl

theorem cell23_3708621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3708621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708621 prefixEnd_3708621 := by exact prefixLift 3708621
  have htrace : WordTrace (prefixWord ++ tailWord_3708621) baseStart_3708621 baseEnd_3708621 := by
    simpa [prefixWord, tailWord_3708621, baseEnd_3708621] using wordTrace_append hprefix tailTrace_3708621
  have hstable : (prefixWord ++ tailWord_3708621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708621).length < 2 ^ (prefixWord ++ tailWord_3708621).sum := by decide
  have hdescent : baseEnd_3708621 < baseStart_3708621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708623 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_3708623 : Nat := 118140960795 + 3708623 * 2 ^ 59
def prefixEnd_3708623 : Nat := 4983230072969 + 3 ^ 40 * 3708623 * 2
def baseEnd_3708623 : Nat := 1904306165319348729156859

theorem tailTrace_3708623 : CollatzResearch.WordTrace tailWord_3708623 prefixEnd_3708623 1904306165319348729156859 := by
  unfold tailWord_3708623
  simp only [CollatzResearch.WordTrace]
  refine ⟨135264593243299728227362523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90176395495533152151575015 135264593243299728227362523)
  ·
    refine ⟨202896889864949592341043785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135264593243299728227362523 202896889864949592341043785)
    ·
      refine ⟨152172667398712194255782839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202896889864949592341043785 152172667398712194255782839)
      ·
        refine ⟨228259001098068291383674259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152172667398712194255782839 228259001098068291383674259)
        ·
          refine ⟨342388501647102437075511389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228259001098068291383674259 342388501647102437075511389)
          ·
            refine ⟨128395688117663413903316771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342388501647102437075511389 128395688117663413903316771)
            ·
              refine ⟨192593532176495120854975157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128395688117663413903316771 192593532176495120854975157)
              ·
                refine ⟨18055643641546417580153921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192593532176495120854975157 18055643641546417580153921)
                ·
                  refine ⟨13541732731159813185115441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18055643641546417580153921 13541732731159813185115441)
                  ·
                    refine ⟨10156299548369859888836581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13541732731159813185115441 10156299548369859888836581)
                    ·
                      refine ⟨1904306165319348729156859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10156299548369859888836581 1904306165319348729156859)
                      ·
                        rfl

theorem cell23_3708623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_3708623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708623 prefixEnd_3708623 := by exact prefixLift 3708623
  have htrace : WordTrace (prefixWord ++ tailWord_3708623) baseStart_3708623 baseEnd_3708623 := by
    simpa [prefixWord, tailWord_3708623, baseEnd_3708623] using wordTrace_append hprefix tailTrace_3708623
  have hstable : (prefixWord ++ tailWord_3708623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708623).length < 2 ^ (prefixWord ++ tailWord_3708623).sum := by decide
  have hdescent : baseEnd_3708623 < baseStart_3708623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708700 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3708700 : Nat := 118140960795 + 3708700 * 2 ^ 59
def prefixEnd_3708700 : Nat := 4983230072969 + 3 ^ 40 * 3708700 * 2
def baseEnd_3708700 : Nat := 1904345703329744927894005

theorem tailTrace_3708700 : CollatzResearch.WordTrace tailWord_3708700 prefixEnd_3708700 1904345703329744927894005 := by
  unfold tailWord_3708700
  simp only [CollatzResearch.WordTrace]
  refine ⟨67633700832010385188957777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90178267776013846918610369 67633700832010385188957777)
  ·
    refine ⟨50725275624007788891718333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67633700832010385188957777 50725275624007788891718333)
    ·
      refine ⟨19021978359002920834394375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50725275624007788891718333 19021978359002920834394375)
      ·
        refine ⟨28532967538504381251591563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19021978359002920834394375 28532967538504381251591563)
        ·
          refine ⟨42799451307756571877387345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28532967538504381251591563 42799451307756571877387345)
          ·
            refine ⟨32099588480817428908040509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42799451307756571877387345 32099588480817428908040509)
            ·
              refine ⟨12037345680306535840515191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32099588480817428908040509 12037345680306535840515191)
              ·
                refine ⟨18056018520459803760772787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12037345680306535840515191 18056018520459803760772787)
                ·
                  refine ⟨27084027780689705641159181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18056018520459803760772787 27084027780689705641159181)
                  ·
                    refine ⟨10156510417758639615434693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27084027780689705641159181 10156510417758639615434693)
                    ·
                      refine ⟨1904345703329744927894005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10156510417758639615434693 1904345703329744927894005)
                      ·
                        rfl

theorem cell23_3708700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3708700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708700 prefixEnd_3708700 := by exact prefixLift 3708700
  have htrace : WordTrace (prefixWord ++ tailWord_3708700) baseStart_3708700 baseEnd_3708700 := by
    simpa [prefixWord, tailWord_3708700, baseEnd_3708700] using wordTrace_append hprefix tailTrace_3708700
  have hstable : (prefixWord ++ tailWord_3708700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708700).length < 2 ^ (prefixWord ++ tailWord_3708700).sum := by decide
  have hdescent : baseEnd_3708700 < baseStart_3708700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708734 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_3708734 : Nat := 118140960795 + 3708734 * 2 ^ 59
def prefixEnd_3708734 : Nat := 4983230072969 + 3 ^ 40 * 3708734 * 2
def baseEnd_3708734 : Nat := 1904363161671997794868849

theorem tailTrace_3708734 : CollatzResearch.WordTrace tailWord_3708734 prefixEnd_3708734 1904363161671997794868849 := by
  unfold tailWord_3708734
  simp only [CollatzResearch.WordTrace]
  refine ⟨16908580218237199273081657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90179094497265062789768837 16908580218237199273081657)
  ·
    refine ⟨12681435163677899454811243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16908580218237199273081657 12681435163677899454811243)
    ·
      refine ⟨19022152745516849182216865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12681435163677899454811243 19022152745516849182216865)
      ·
        refine ⟨14266614559137636886662649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19022152745516849182216865 14266614559137636886662649)
        ·
          refine ⟨10699960919353227664996987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14266614559137636886662649 10699960919353227664996987)
          ·
            refine ⟨16049941379029841497495481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10699960919353227664996987 16049941379029841497495481)
            ·
              refine ⟨12037456034272381123121611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16049941379029841497495481 12037456034272381123121611)
              ·
                refine ⟨18056184051408571684682417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12037456034272381123121611 18056184051408571684682417)
                ·
                  refine ⟨13542138038556428763511813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18056184051408571684682417 13542138038556428763511813)
                  ·
                    refine ⟨2539150882229330393158465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13542138038556428763511813 2539150882229330393158465)
                    ·
                      refine ⟨1904363161671997794868849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2539150882229330393158465 1904363161671997794868849)
                      ·
                        rfl

theorem cell23_3708734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_3708734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708734 prefixEnd_3708734 := by exact prefixLift 3708734
  have htrace : WordTrace (prefixWord ++ tailWord_3708734) baseStart_3708734 baseEnd_3708734 := by
    simpa [prefixWord, tailWord_3708734, baseEnd_3708734] using wordTrace_append hprefix tailTrace_3708734
  have hstable : (prefixWord ++ tailWord_3708734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708734).length < 2 ^ (prefixWord ++ tailWord_3708734).sum := by decide
  have hdescent : baseEnd_3708734 < baseStart_3708734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708778 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3708778 : Nat := 118140960795 + 3708778 * 2 ^ 59
def prefixEnd_3708778 : Nat := 4983230072969 + 3 ^ 40 * 3708778 * 2
def baseEnd_3708778 : Nat := 634795251606931874239549

theorem tailTrace_3708778 : CollatzResearch.WordTrace tailWord_3708778 prefixEnd_3708778 634795251606931874239549 := by
  unfold tailWord_3708778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33817561639434547424813747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90180164371825459799503325 33817561639434547424813747)
  ·
    refine ⟨50726342459151821137220621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33817561639434547424813747 50726342459151821137220621)
    ·
      refine ⟨19022378422181932926457733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50726342459151821137220621 19022378422181932926457733)
      ·
        refine ⟨3566695954159112423710825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19022378422181932926457733 3566695954159112423710825)
        ·
          refine ⟨2675021965619334317783119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3566695954159112423710825 2675021965619334317783119)
          ·
            refine ⟨4012532948429001476674679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675021965619334317783119 4012532948429001476674679)
            ·
              refine ⟨6018799422643502215012019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012532948429001476674679 6018799422643502215012019)
              ·
                refine ⟨9028199133965253322518029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6018799422643502215012019 9028199133965253322518029)
                ·
                  refine ⟨3385574675236969995944261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9028199133965253322518029 3385574675236969995944261)
                  ·
                    refine ⟨634795251606931874239549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3385574675236969995944261 634795251606931874239549)
                    ·
                      rfl

theorem cell23_3708778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3708778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708778 prefixEnd_3708778 := by exact prefixLift 3708778
  have htrace : WordTrace (prefixWord ++ tailWord_3708778) baseStart_3708778 baseEnd_3708778 := by
    simpa [prefixWord, tailWord_3708778, baseEnd_3708778] using wordTrace_append hprefix tailTrace_3708778
  have hstable : (prefixWord ++ tailWord_3708778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708778).length < 2 ^ (prefixWord ++ tailWord_3708778).sum := by decide
  have hdescent : baseEnd_3708778 < baseStart_3708778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708800 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 1, 6]
def baseStart_3708800 : Nat := 118140960795 + 3708800 * 2 ^ 59
def prefixEnd_3708800 : Nat := 4983230072969 + 3 ^ 40 * 3708800 * 2
def baseEnd_3708800 : Nat := 634799017131731512214515

theorem tailTrace_3708800 : CollatzResearch.WordTrace tailWord_3708800 prefixEnd_3708800 634799017131731512214515 := by
  unfold tailWord_3708800
  simp only [CollatzResearch.WordTrace]
  refine ⟨67635524481829243728277927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90180699309105658304370569 67635524481829243728277927)
  ·
    refine ⟨101453286722743865592416891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67635524481829243728277927 101453286722743865592416891)
    ·
      refine ⟨152179930084115798388625337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101453286722743865592416891 152179930084115798388625337)
      ·
        refine ⟨114134947563086848791469003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152179930084115798388625337 114134947563086848791469003)
        ·
          refine ⟨171202421344630273187203505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114134947563086848791469003 171202421344630273187203505)
          ·
            refine ⟨128401816008472704890402629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171202421344630273187203505 128401816008472704890402629)
            ·
              refine ⟨24075340501588632166950493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128401816008472704890402629 24075340501588632166950493)
              ·
                refine ⟨9028252688095737062606435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24075340501588632166950493 9028252688095737062606435)
                ·
                  refine ⟨13542379032143605593909653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9028252688095737062606435 13542379032143605593909653)
                  ·
                    refine ⟨634799017131731512214515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13542379032143605593909653 634799017131731512214515)
                    ·
                      rfl

theorem cell23_3708800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_3708800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708800 prefixEnd_3708800 := by exact prefixLift 3708800
  have htrace : WordTrace (prefixWord ++ tailWord_3708800) baseStart_3708800 baseEnd_3708800 := by
    simpa [prefixWord, tailWord_3708800, baseEnd_3708800] using wordTrace_append hprefix tailTrace_3708800
  have hstable : (prefixWord ++ tailWord_3708800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708800).length < 2 ^ (prefixWord ++ tailWord_3708800).sum := by decide
  have hdescent : baseEnd_3708800 < baseStart_3708800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708850 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3708850 : Nat := 118140960795 + 3708850 * 2 ^ 59
def prefixEnd_3708850 : Nat := 4983230072969 + 3 ^ 40 * 3708850 * 2
def baseEnd_3708850 : Nat := 1904422725427919341018315

theorem tailTrace_3708850 : CollatzResearch.WordTrace tailWord_3708850 prefixEnd_3708850 1904422725427919341018315 := by
  unfold tailWord_3708850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33818218153369336498969001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90181915075651563997250669 33818218153369336498969001)
  ·
    refine ⟨25363663615027002374226751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33818218153369336498969001 25363663615027002374226751)
    ·
      refine ⟨38045495422540503561340127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25363663615027002374226751 38045495422540503561340127)
      ·
        refine ⟨57068243133810755342010191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38045495422540503561340127 57068243133810755342010191)
        ·
          refine ⟨85602364700716133013015287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57068243133810755342010191 85602364700716133013015287)
          ·
            refine ⟨128403547051074199519522931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85602364700716133013015287 128403547051074199519522931)
            ·
              refine ⟨192605320576611299279284397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128403547051074199519522931 192605320576611299279284397)
              ·
                refine ⟨72226995216229237229731649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192605320576611299279284397 72226995216229237229731649)
                ·
                  refine ⟨54170246412171927922298737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72226995216229237229731649 54170246412171927922298737)
                  ·
                    refine ⟨40627684809128945941724053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54170246412171927922298737 40627684809128945941724053)
                    ·
                      refine ⟨1904422725427919341018315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40627684809128945941724053 1904422725427919341018315)
                      ·
                        rfl

theorem cell23_3708850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3708850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708850 prefixEnd_3708850 := by exact prefixLift 3708850
  have htrace : WordTrace (prefixWord ++ tailWord_3708850) baseStart_3708850 baseEnd_3708850 := by
    simpa [prefixWord, tailWord_3708850, baseEnd_3708850] using wordTrace_append hprefix tailTrace_3708850
  have hstable : (prefixWord ++ tailWord_3708850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708850).length < 2 ^ (prefixWord ++ tailWord_3708850).sum := by decide
  have hdescent : baseEnd_3708850 < baseStart_3708850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708892 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3708892 : Nat := 118140960795 + 3708892 * 2 ^ 59
def prefixEnd_3708892 : Nat := 4983230072969 + 3 ^ 40 * 3708892 * 2
def baseEnd_3708892 : Nat := 1904444291615408176693123

theorem tailTrace_3708892 : CollatzResearch.WordTrace tailWord_3708892 prefixEnd_3708892 1904444291615408176693123 := by
  unfold tailWord_3708892
  simp only [CollatzResearch.WordTrace]
  refine ⟨67637202239662593584452465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90182936319550124779269953 67637202239662593584452465)
  ·
    refine ⟨50727901679746945188339349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67637202239662593584452465 50727901679746945188339349)
    ·
      refine ⟨2377870391238138055703407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50727901679746945188339349 2377870391238138055703407)
      ·
        refine ⟨3566805586857207083555111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377870391238138055703407 3566805586857207083555111)
        ·
          refine ⟨5350208380285810625332667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566805586857207083555111 5350208380285810625332667)
          ·
            refine ⟨8025312570428715937999001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350208380285810625332667 8025312570428715937999001)
            ·
              refine ⟨6018984427821536953499251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8025312570428715937999001 6018984427821536953499251)
              ·
                refine ⟨9028476641732305430248877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6018984427821536953499251 9028476641732305430248877)
                ·
                  refine ⟨3385678740649614536343329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9028476641732305430248877 3385678740649614536343329)
                  ·
                    refine ⟨2539259055487210902257497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385678740649614536343329 2539259055487210902257497)
                    ·
                      refine ⟨1904444291615408176693123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2539259055487210902257497 1904444291615408176693123)
                      ·
                        rfl

theorem cell23_3708892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3708892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708892 prefixEnd_3708892 := by exact prefixLift 3708892
  have htrace : WordTrace (prefixWord ++ tailWord_3708892) baseStart_3708892 baseEnd_3708892 := by
    simpa [prefixWord, tailWord_3708892, baseEnd_3708892] using wordTrace_append hprefix tailTrace_3708892
  have hstable : (prefixWord ++ tailWord_3708892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708892).length < 2 ^ (prefixWord ++ tailWord_3708892).sum := by decide
  have hdescent : baseEnd_3708892 < baseStart_3708892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708947 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 3]
def baseStart_3708947 : Nat := 118140960795 + 3708947 * 2 ^ 59
def prefixEnd_3708947 : Nat := 4983230072969 + 3 ^ 40 * 3708947 * 2
def baseEnd_3708947 : Nat := 1904472533051405461505369

theorem tailTrace_3708947 : CollatzResearch.WordTrace tailWord_3708947 prefixEnd_3708947 1904472533051405461505369 := by
  unfold tailWord_3708947
  simp only [CollatzResearch.WordTrace]
  refine ⟨135276410494125931562157095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90184273662750621041438063 135276410494125931562157095)
  ·
    refine ⟨202914615741188897343235643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135276410494125931562157095 202914615741188897343235643)
    ·
      refine ⟨304371923611783346014853465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202914615741188897343235643 304371923611783346014853465)
      ·
        refine ⟨228278942708837509511140099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304371923611783346014853465 228278942708837509511140099)
        ·
          refine ⟨342418414063256264266710149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228278942708837509511140099 342418414063256264266710149)
          ·
            refine ⟨64203452636860549550008153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342418414063256264266710149 64203452636860549550008153)
            ·
              refine ⟨48152589477645412162506115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64203452636860549550008153 48152589477645412162506115)
              ·
                refine ⟨72228884216468118243759173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48152589477645412162506115 72228884216468118243759173)
                ·
                  refine ⟨13542915790587772170704845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72228884216468118243759173 13542915790587772170704845)
                  ·
                    refine ⟨5078593421470414564014317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13542915790587772170704845 5078593421470414564014317)
                    ·
                      refine ⟨1904472533051405461505369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5078593421470414564014317 1904472533051405461505369)
                      ·
                        rfl

theorem cell23_3708947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_3708947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708947 prefixEnd_3708947 := by exact prefixLift 3708947
  have htrace : WordTrace (prefixWord ++ tailWord_3708947) baseStart_3708947 baseEnd_3708947 := by
    simpa [prefixWord, tailWord_3708947, baseEnd_3708947] using wordTrace_append hprefix tailTrace_3708947
  have hstable : (prefixWord ++ tailWord_3708947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708947).length < 2 ^ (prefixWord ++ tailWord_3708947).sum := by decide
  have hdescent : baseEnd_3708947 < baseStart_3708947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708954 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 7]
def baseStart_3708954 : Nat := 118140960795 + 3708954 * 2 ^ 59
def prefixEnd_3708954 : Nat := 4983230072969 + 3 ^ 40 * 3708954 * 2
def baseEnd_3708954 : Nat := 211608458601776326013093

theorem tailTrace_3708954 : CollatzResearch.WordTrace tailWord_3708954 prefixEnd_3708954 211608458601776326013093 := by
  unfold tailWord_3708954
  simp only [CollatzResearch.WordTrace]
  refine ⟨33819166451275142939415479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90184443870067047838441277 33819166451275142939415479)
  ·
    refine ⟨50728749676912714409123219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33819166451275142939415479 50728749676912714409123219)
    ·
      refine ⟨76093124515369071613684829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50728749676912714409123219 76093124515369071613684829)
      ·
        refine ⟨28534921693263401855131811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76093124515369071613684829 28534921693263401855131811)
        ·
          refine ⟨42802382539895102782697717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28534921693263401855131811 42802382539895102782697717)
          ·
            refine ⟨4012723363115165885877911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42802382539895102782697717 4012723363115165885877911)
            ·
              refine ⟨6019085044672748828816867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012723363115165885877911 6019085044672748828816867)
              ·
                refine ⟨9028627567009123243225301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019085044672748828816867 9028627567009123243225301)
                ·
                  refine ⟨211608458601776326013093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9028627567009123243225301 211608458601776326013093)
                  ·
                    rfl

theorem cell23_3708954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_3708954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708954 prefixEnd_3708954 := by exact prefixLift 3708954
  have htrace : WordTrace (prefixWord ++ tailWord_3708954) baseStart_3708954 baseEnd_3708954 := by
    simpa [prefixWord, tailWord_3708954, baseEnd_3708954] using wordTrace_append hprefix tailTrace_3708954
  have hstable : (prefixWord ++ tailWord_3708954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708954).length < 2 ^ (prefixWord ++ tailWord_3708954).sum := by decide
  have hdescent : baseEnd_3708954 < baseStart_3708954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708965 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 2, 2, 2]
def baseStart_3708965 : Nat := 118140960795 + 3708965 * 2 ^ 59
def prefixEnd_3708965 : Nat := 4983230072969 + 3 ^ 40 * 3708965 * 2
def baseEnd_3708965 : Nat := 1904481775703186391080287

theorem tailTrace_3708965 : CollatzResearch.WordTrace tailWord_3708965 prefixEnd_3708965 1904481775703186391080287 := by
  unfold tailWord_3708965
  simp only [CollatzResearch.WordTrace]
  refine ⟨135277067008060720636312349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90184711338707147090874899 135277067008060720636312349)
  ·
    refine ⟨50728900128022770238617131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135277067008060720636312349 50728900128022770238617131)
    ·
      refine ⟨76093350192034155357925697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50728900128022770238617131 76093350192034155357925697)
      ·
        refine ⟨57070012644025616518444273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76093350192034155357925697 57070012644025616518444273)
        ·
          refine ⟨42802509483019212388833205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57070012644025616518444273 42802509483019212388833205)
          ·
            refine ⟨4012735264033051161453113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42802509483019212388833205 4012735264033051161453113)
            ·
              refine ⟨3009551448024788371089835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012735264033051161453113 3009551448024788371089835)
              ·
                refine ⟨4514327172037182556634753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009551448024788371089835 4514327172037182556634753)
                ·
                  refine ⟨3385745379027886917476065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514327172037182556634753 3385745379027886917476065)
                  ·
                    refine ⟨2539309034270915188107049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385745379027886917476065 2539309034270915188107049)
                    ·
                      refine ⟨1904481775703186391080287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2539309034270915188107049 1904481775703186391080287)
                      ·
                        rfl

theorem cell23_3708965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_3708965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708965 prefixEnd_3708965 := by exact prefixLift 3708965
  have htrace : WordTrace (prefixWord ++ tailWord_3708965) baseStart_3708965 baseEnd_3708965 := by
    simpa [prefixWord, tailWord_3708965, baseEnd_3708965] using wordTrace_append hprefix tailTrace_3708965
  have hstable : (prefixWord ++ tailWord_3708965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708965).length < 2 ^ (prefixWord ++ tailWord_3708965).sum := by decide
  have hdescent : baseEnd_3708965 < baseStart_3708965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708987 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 4]
def baseStart_3708987 : Nat := 118140960795 + 3708987 * 2 ^ 59
def prefixEnd_3708987 : Nat := 4983230072969 + 3 ^ 40 * 3708987 * 2
def baseEnd_3708987 : Nat := 1904493072277585305005185

theorem tailTrace_3708987 : CollatzResearch.WordTrace tailWord_3708987 prefixEnd_3708987 1904493072277585305005185 := by
  unfold tailWord_3708987
  simp only [CollatzResearch.WordTrace]
  refine ⟨135277869413981018393613215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90185246275987345595742143 135277869413981018393613215)
  ·
    refine ⟨202916804120971527590419823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135277869413981018393613215 202916804120971527590419823)
    ·
      refine ⟨304375206181457291385629735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202916804120971527590419823 304375206181457291385629735)
      ·
        refine ⟨456562809272185937078444603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304375206181457291385629735 456562809272185937078444603)
        ·
          refine ⟨684844213908278905617666905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456562809272185937078444603 684844213908278905617666905)
          ·
            refine ⟨513633160431209179213250179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684844213908278905617666905 513633160431209179213250179)
            ·
              refine ⟨770449740646813768819875269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513633160431209179213250179 770449740646813768819875269)
              ·
                refine ⟨144459326371277581653726613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 770449740646813768819875269 144459326371277581653726613)
                ·
                  refine ⟨6771530923653636640018435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144459326371277581653726613 6771530923653636640018435)
                  ·
                    refine ⟨10157296385480454960027653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6771530923653636640018435 10157296385480454960027653)
                    ·
                      refine ⟨1904493072277585305005185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10157296385480454960027653 1904493072277585305005185)
                      ·
                        rfl

theorem cell23_3708987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 4].length) (baseStart_3708987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3708987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3708987 prefixEnd_3708987 := by exact prefixLift 3708987
  have htrace : WordTrace (prefixWord ++ tailWord_3708987) baseStart_3708987 baseEnd_3708987 := by
    simpa [prefixWord, tailWord_3708987, baseEnd_3708987] using wordTrace_append hprefix tailTrace_3708987
  have hstable : (prefixWord ++ tailWord_3708987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708987).length < 2 ^ (prefixWord ++ tailWord_3708987).sum := by decide
  have hdescent : baseEnd_3708987 < baseStart_3708987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709004 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3709004 : Nat := 118140960795 + 3709004 * 2 ^ 59
def prefixEnd_3709004 : Nat := 4983230072969 + 3 ^ 40 * 3709004 * 2
def baseEnd_3709004 : Nat := 1904501801448711738492607

theorem tailTrace_3709004 : CollatzResearch.WordTrace tailWord_3709004 prefixEnd_3709004 1904501801448711738492607 := by
  unfold tailWord_3709004
  simp only [CollatzResearch.WordTrace]
  refine ⟨67639244727459715148491033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90185659636612953531321377 67639244727459715148491033)
  ·
    refine ⟨50729433545594786361368275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67639244727459715148491033 50729433545594786361368275)
    ·
      refine ⟨76094150318392179542052413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50729433545594786361368275 76094150318392179542052413)
      ·
        refine ⟨28535306369397067328269655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76094150318392179542052413 28535306369397067328269655)
        ·
          refine ⟨42802959554095600992404483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28535306369397067328269655 42802959554095600992404483)
          ·
            refine ⟨64204439331143401488606725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42802959554095600992404483 64204439331143401488606725)
            ·
              refine ⟨12038332374589387779113761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64204439331143401488606725 12038332374589387779113761)
              ·
                refine ⟨9028749280942040834335321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12038332374589387779113761 9028749280942040834335321)
                ·
                  refine ⟨6771561960706530625751491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9028749280942040834335321 6771561960706530625751491)
                  ·
                    refine ⟨10157342941059795938627237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6771561960706530625751491 10157342941059795938627237)
                    ·
                      refine ⟨1904501801448711738492607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10157342941059795938627237 1904501801448711738492607)
                      ·
                        rfl

theorem cell23_3709004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3709004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709004 prefixEnd_3709004 := by exact prefixLift 3709004
  have htrace : WordTrace (prefixWord ++ tailWord_3709004) baseStart_3709004 baseEnd_3709004 := by
    simpa [prefixWord, tailWord_3709004, baseEnd_3709004] using wordTrace_append hprefix tailTrace_3709004
  have hstable : (prefixWord ++ tailWord_3709004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709004).length < 2 ^ (prefixWord ++ tailWord_3709004).sum := by decide
  have hdescent : baseEnd_3709004 < baseStart_3709004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709061 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 6]
def baseStart_3709061 : Nat := 118140960795 + 3709061 * 2 ^ 59
def prefixEnd_3709061 : Nat := 4983230072969 + 3 ^ 40 * 3709061 * 2
def baseEnd_3709061 : Nat := 211614563316224223942205

theorem tailTrace_3709061 : CollatzResearch.WordTrace tailWord_3709061 prefixEnd_3709061 211614563316224223942205 := by
  unfold tailWord_3709061
  simp only [CollatzResearch.WordTrace]
  refine ⟨135280568415712929031807037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90187045610475286021204691 135280568415712929031807037)
  ·
    refine ⟨50730213155892348386927639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135280568415712929031807037 50730213155892348386927639)
    ·
      refine ⟨76095319733838522580391459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50730213155892348386927639 76095319733838522580391459)
      ·
        refine ⟨114142979600757783870587189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76095319733838522580391459 114142979600757783870587189)
        ·
          refine ⟨10700904337571042237867549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114142979600757783870587189 10700904337571042237867549)
          ·
            refine ⟨4012839126589140839200331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10700904337571042237867549 4012839126589140839200331)
            ·
              refine ⟨6019258689883711258800497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012839126589140839200331 6019258689883711258800497)
              ·
                refine ⟨4514444017412783444100373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6019258689883711258800497 4514444017412783444100373)
                ·
                  refine ⟨211614563316224223942205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4514444017412783444100373 211614563316224223942205)
                  ·
                    rfl

theorem cell23_3709061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_3709061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709061 prefixEnd_3709061 := by exact prefixLift 3709061
  have htrace : WordTrace (prefixWord ++ tailWord_3709061) baseStart_3709061 baseEnd_3709061 := by
    simpa [prefixWord, tailWord_3709061, baseEnd_3709061] using wordTrace_append hprefix tailTrace_3709061
  have hstable : (prefixWord ++ tailWord_3709061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709061).length < 2 ^ (prefixWord ++ tailWord_3709061).sum := by decide
  have hdescent : baseEnd_3709061 < baseStart_3709061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709064 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3709064 : Nat := 118140960795 + 3709064 * 2 ^ 59
def prefixEnd_3709064 : Nat := 4983230072969 + 3 ^ 40 * 3709064 * 2
def baseEnd_3709064 : Nat := 1904532610287981503742331

theorem tailTrace_3709064 : CollatzResearch.WordTrace tailWord_3709064 prefixEnd_3709064 1904532610287981503742331 := by
  unfold tailWord_3709064
  simp only [CollatzResearch.WordTrace]
  refine ⟨67640338917351030272083123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90187118556468040362777497 67640338917351030272083123)
  ·
    refine ⟨101460508376026545408124685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67640338917351030272083123 101460508376026545408124685)
    ·
      refine ⟨38047690641009954528046757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101460508376026545408124685 38047690641009954528046757)
      ·
        refine ⟨7133941995189366474008767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38047690641009954528046757 7133941995189366474008767)
        ·
          refine ⟨10700912992784049711013151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7133941995189366474008767 10700912992784049711013151)
          ·
            refine ⟨16051369489176074566519727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10700912992784049711013151 16051369489176074566519727)
            ·
              refine ⟨24077054233764111849779591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16051369489176074566519727 24077054233764111849779591)
              ·
                refine ⟨36115581350646167774669387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24077054233764111849779591 36115581350646167774669387)
                ·
                  refine ⟨54173372025969251662004081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36115581350646167774669387 54173372025969251662004081)
                  ·
                    refine ⟨40630029019476938746503061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54173372025969251662004081 40630029019476938746503061)
                    ·
                      refine ⟨1904532610287981503742331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40630029019476938746503061 1904532610287981503742331)
                      ·
                        rfl

theorem cell23_3709064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3709064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709064 prefixEnd_3709064 := by exact prefixLift 3709064
  have htrace : WordTrace (prefixWord ++ tailWord_3709064) baseStart_3709064 baseEnd_3709064 := by
    simpa [prefixWord, tailWord_3709064, baseEnd_3709064] using wordTrace_append hprefix tailTrace_3709064
  have hstable : (prefixWord ++ tailWord_3709064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709064).length < 2 ^ (prefixWord ++ tailWord_3709064).sum := by decide
  have hdescent : baseEnd_3709064 < baseStart_3709064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709097 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_3709097 : Nat := 118140960795 + 3709097 * 2 ^ 59
def prefixEnd_3709097 : Nat := 4983230072969 + 3 ^ 40 * 3709097 * 2
def baseEnd_3709097 : Nat := 1904549555149579874629679

theorem tailTrace_3709097 : CollatzResearch.WordTrace tailWord_3709097 prefixEnd_3709097 1904549555149579874629679 := by
  unfold tailWord_3709097
  simp only [CollatzResearch.WordTrace]
  refine ⟨135281881443582507180117545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90187920962388338120078363 135281881443582507180117545)
  ·
    refine ⟨101461411082686880385088159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135281881443582507180117545 101461411082686880385088159)
    ·
      refine ⟨152192116624030320577632239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101461411082686880385088159 152192116624030320577632239)
      ·
        refine ⟨228288174936045480866448359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152192116624030320577632239 228288174936045480866448359)
        ·
          refine ⟨342432262404068221299672539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228288174936045480866448359 342432262404068221299672539)
          ·
            refine ⟨513648393606102331949508809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342432262404068221299672539 513648393606102331949508809)
            ·
              refine ⟨385236295204576748962131607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513648393606102331949508809 385236295204576748962131607)
              ·
                refine ⟨577854442806865123443197411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385236295204576748962131607 577854442806865123443197411)
                ·
                  refine ⟨866781664210297685164796117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577854442806865123443197411 866781664210297685164796117)
                  ·
                    refine ⟨20315195254928851996049909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 866781664210297685164796117 20315195254928851996049909)
                    ·
                      refine ⟨1904549555149579874629679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20315195254928851996049909 1904549555149579874629679)
                      ·
                        rfl

theorem cell23_3709097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_3709097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709097 prefixEnd_3709097 := by exact prefixLift 3709097
  have htrace : WordTrace (prefixWord ++ tailWord_3709097) baseStart_3709097 baseEnd_3709097 := by
    simpa [prefixWord, tailWord_3709097, baseEnd_3709097] using wordTrace_append hprefix tailTrace_3709097
  have hstable : (prefixWord ++ tailWord_3709097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709097).length < 2 ^ (prefixWord ++ tailWord_3709097).sum := by decide
  have hdescent : baseEnd_3709097 < baseStart_3709097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709111 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_3709111 : Nat := 118140960795 + 3709111 * 2 ^ 59
def prefixEnd_3709111 : Nat := 4983230072969 + 3 ^ 40 * 3709111 * 2
def baseEnd_3709111 : Nat := 1904556743878742819854615

theorem tailTrace_3709111 : CollatzResearch.WordTrace tailWord_3709111 prefixEnd_3709111 1904556743878742819854615 := by
  unfold tailWord_3709111
  simp only [CollatzResearch.WordTrace]
  refine ⟨135282392065531787571127187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90188261377021191714084791 135282392065531787571127187)
  ·
    refine ⟨202923588098297681356690781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135282392065531787571127187 202923588098297681356690781)
    ·
      refine ⟨76096345536861630508759043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202923588098297681356690781 76096345536861630508759043)
      ·
        refine ⟨114144518305292445763138565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76096345536861630508759043 114144518305292445763138565)
        ·
          refine ⟨21402097182242333580588481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114144518305292445763138565 21402097182242333580588481)
          ·
            refine ⟨16051572886681750185441361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21402097182242333580588481 16051572886681750185441361)
            ·
              refine ⟨12038679665011312639081021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16051572886681750185441361 12038679665011312639081021)
              ·
                refine ⟨4514504874379242239655383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12038679665011312639081021 4514504874379242239655383)
                ·
                  refine ⟨6771757311568863359483075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514504874379242239655383 6771757311568863359483075)
                  ·
                    refine ⟨10157635967353295039224613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6771757311568863359483075 10157635967353295039224613)
                    ·
                      refine ⟨1904556743878742819854615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10157635967353295039224613 1904556743878742819854615)
                      ·
                        rfl

theorem cell23_3709111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_3709111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709111 prefixEnd_3709111 := by exact prefixLift 3709111
  have htrace : WordTrace (prefixWord ++ tailWord_3709111) baseStart_3709111 baseEnd_3709111 := by
    simpa [prefixWord, tailWord_3709111, baseEnd_3709111] using wordTrace_append hprefix tailTrace_3709111
  have hstable : (prefixWord ++ tailWord_3709111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709111).length < 2 ^ (prefixWord ++ tailWord_3709111).sum := by decide
  have hdescent : baseEnd_3709111 < baseStart_3709111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709114 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_3709114 : Nat := 118140960795 + 3709114 * 2 ^ 59
def prefixEnd_3709114 : Nat := 4983230072969 + 3 ^ 40 * 3709114 * 2
def baseEnd_3709114 : Nat := 1904558284320706308117101

theorem tailTrace_3709114 : CollatzResearch.WordTrace tailWord_3709114 prefixEnd_3709114 1904558284320706308117101 := by
  unfold tailWord_3709114
  simp only [CollatzResearch.WordTrace]
  refine ⟨33820625371130229770871599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90188334323013946055657597 33820625371130229770871599)
  ·
    refine ⟨50730938056695344656307399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33820625371130229770871599 50730938056695344656307399)
    ·
      refine ⟨76096407085043016984461099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50730938056695344656307399 76096407085043016984461099)
      ·
        refine ⟨114144610627564525476691649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76096407085043016984461099 114144610627564525476691649)
        ·
          refine ⟨85608457970673394107518737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114144610627564525476691649 85608457970673394107518737)
          ·
            refine ⟨64206343478005045580639053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85608457970673394107518737 64206343478005045580639053)
            ·
              refine ⟨24077378804251892092739645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64206343478005045580639053 24077378804251892092739645)
              ·
                refine ⟨9029017051594459534777367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24077378804251892092739645 9029017051594459534777367)
                ·
                  refine ⟨13543525577391689302166051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9029017051594459534777367 13543525577391689302166051)
                  ·
                    refine ⟨20315288366087533953249077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13543525577391689302166051 20315288366087533953249077)
                    ·
                      refine ⟨1904558284320706308117101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20315288366087533953249077 1904558284320706308117101)
                      ·
                        rfl

theorem cell23_3709114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_3709114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709114 prefixEnd_3709114 := by exact prefixLift 3709114
  have htrace : WordTrace (prefixWord ++ tailWord_3709114) baseStart_3709114 baseEnd_3709114 := by
    simpa [prefixWord, tailWord_3709114, baseEnd_3709114] using wordTrace_append hprefix tailTrace_3709114
  have hstable : (prefixWord ++ tailWord_3709114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709114).length < 2 ^ (prefixWord ++ tailWord_3709114).sum := by decide
  have hdescent : baseEnd_3709114 < baseStart_3709114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709122 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3709122 : Nat := 118140960795 + 3709122 * 2 ^ 59
def prefixEnd_3709122 : Nat := 4983230072969 + 3 ^ 40 * 3709122 * 2
def baseEnd_3709122 : Nat := 1904562392165942276817065

theorem tailTrace_3709122 : CollatzResearch.WordTrace tailWord_3709122 prefixEnd_3709122 1904562392165942276817065 := by
  unfold tailWord_3709122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33820698317122984112444405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90188528845661290966518413 33820698317122984112444405)
  ·
    refine ⟨3170690467230279760541663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33820698317122984112444405 3170690467230279760541663)
    ·
      refine ⟨4756035700845419640812495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170690467230279760541663 4756035700845419640812495)
      ·
        refine ⟨7134053551268129461218743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4756035700845419640812495 7134053551268129461218743)
        ·
          refine ⟨10701080326902194191828115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7134053551268129461218743 10701080326902194191828115)
          ·
            refine ⟨16051620490353291287742173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701080326902194191828115 16051620490353291287742173)
            ·
              refine ⟨6019357683882484232903315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16051620490353291287742173 6019357683882484232903315)
              ·
                refine ⟨9029036525823726349354973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019357683882484232903315 9029036525823726349354973)
                ·
                  refine ⟨3385888697183897381008115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9029036525823726349354973 3385888697183897381008115)
                  ·
                    refine ⟨5078833045775846071512173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3385888697183897381008115 5078833045775846071512173)
                    ·
                      refine ⟨1904562392165942276817065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5078833045775846071512173 1904562392165942276817065)
                      ·
                        rfl

theorem cell23_3709122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3709122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709122 prefixEnd_3709122 := by exact prefixLift 3709122
  have htrace : WordTrace (prefixWord ++ tailWord_3709122) baseStart_3709122 baseEnd_3709122 := by
    simpa [prefixWord, tailWord_3709122, baseEnd_3709122] using wordTrace_append hprefix tailTrace_3709122
  have hstable : (prefixWord ++ tailWord_3709122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709122).length < 2 ^ (prefixWord ++ tailWord_3709122).sum := by decide
  have hdescent : baseEnd_3709122 < baseStart_3709122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709134 : List Nat := [4, 1, 1, 1, 4, 1, 1, 10]
def baseStart_3709134 : Nat := 118140960795 + 3709134 * 2 ^ 59
def prefixEnd_3709134 : Nat := 4983230072969 + 3 ^ 40 * 3709134 * 2
def baseEnd_3709134 : Nat := 70539576071622082587667

theorem tailTrace_3709134 : CollatzResearch.WordTrace tailWord_3709134 prefixEnd_3709134 70539576071622082587667 := by
  unfold tailWord_3709134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910403868056057812401807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90188820629632308332809637 16910403868056057812401807)
  ·
    refine ⟨25365605802084086718602711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16910403868056057812401807 25365605802084086718602711)
    ·
      refine ⟨38048408703126130077904067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25365605802084086718602711 38048408703126130077904067)
      ·
        refine ⟨57072613054689195116856101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38048408703126130077904067 57072613054689195116856101)
        ·
          refine ⟨10701114947754224084410519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57072613054689195116856101 10701114947754224084410519)
          ·
            refine ⟨16051672421631336126615779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701114947754224084410519 16051672421631336126615779)
            ·
              refine ⟨24077508632447004189923669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16051672421631336126615779 24077508632447004189923669)
              ·
                refine ⟨70539576071622082587667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24077508632447004189923669 70539576071622082587667)
                ·
                  rfl

theorem cell23_3709134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_3709134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709134 prefixEnd_3709134 := by exact prefixLift 3709134
  have htrace : WordTrace (prefixWord ++ tailWord_3709134) baseStart_3709134 baseEnd_3709134 := by
    simpa [prefixWord, tailWord_3709134, baseEnd_3709134] using wordTrace_append hprefix tailTrace_3709134
  have hstable : (prefixWord ++ tailWord_3709134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709134).length < 2 ^ (prefixWord ++ tailWord_3709134).sum := by decide
  have hdescent : baseEnd_3709134 < baseStart_3709134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709138 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3709138 : Nat := 118140960795 + 3709138 * 2 ^ 59
def prefixEnd_3709138 : Nat := 4983230072969 + 3 ^ 40 * 3709138 * 2
def baseEnd_3709138 : Nat := 634856869285471404738997

theorem tailTrace_3709138 : CollatzResearch.WordTrace tailWord_3709138 prefixEnd_3709138 634856869285471404738997 := by
  unfold tailWord_3709138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33820844209108492795590017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90188917890955980788240045 33820844209108492795590017)
  ·
    refine ⟨25365633156831369596692513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33820844209108492795590017 25365633156831369596692513)
    ·
      refine ⟨19024224867623527197519385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25365633156831369596692513 19024224867623527197519385)
      ·
        refine ⟨14268168650717645398139539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19024224867623527197519385 14268168650717645398139539)
        ·
          refine ⟨21402252976076468097209309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14268168650717645398139539 21402252976076468097209309)
          ·
            refine ⟨8025844866028675536453491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21402252976076468097209309 8025844866028675536453491)
            ·
              refine ⟨12038767299043013304680237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8025844866028675536453491 12038767299043013304680237)
              ·
                refine ⟨4514537737141129989255089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12038767299043013304680237 4514537737141129989255089)
                ·
                  refine ⟨3385903302855847491941317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514537737141129989255089 3385903302855847491941317)
                  ·
                    refine ⟨634856869285471404738997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3385903302855847491941317 634856869285471404738997)
                    ·
                      rfl

theorem cell23_3709138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3709138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709138 prefixEnd_3709138 := by exact prefixLift 3709138
  have htrace : WordTrace (prefixWord ++ tailWord_3709138) baseStart_3709138 baseEnd_3709138 := by
    simpa [prefixWord, tailWord_3709138, baseEnd_3709138] using wordTrace_append hprefix tailTrace_3709138
  have hstable : (prefixWord ++ tailWord_3709138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709138).length < 2 ^ (prefixWord ++ tailWord_3709138).sum := by decide
  have hdescent : baseEnd_3709138 < baseStart_3709138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709165 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_3709165 : Nat := 118140960795 + 3709165 * 2 ^ 59
def prefixEnd_3709165 : Nat := 4983230072969 + 3 ^ 40 * 3709165 * 2
def baseEnd_3709165 : Nat := 1904584471834085608579367

theorem tailTrace_3709165 : CollatzResearch.WordTrace tailWord_3709165 prefixEnd_3709165 1904584471834085608579367 := by
  unfold tailWord_3709165
  simp only [CollatzResearch.WordTrace]
  refine ⟨135284361607336154793592949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90189574404890769862395299 135284361607336154793592949)
  ·
    refine ⟨12682908900687764511899339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135284361607336154793592949 12682908900687764511899339)
    ·
      refine ⟨19024363351031646767849009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12682908900687764511899339 19024363351031646767849009)
      ·
        refine ⟨14268272513273735075886757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19024363351031646767849009 14268272513273735075886757)
        ·
          refine ⟨2675301096238825326728767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14268272513273735075886757 2675301096238825326728767)
          ·
            refine ⟨4012951644358237990093151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675301096238825326728767 4012951644358237990093151)
            ·
              refine ⟨6019427466537356985139727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012951644358237990093151 6019427466537356985139727)
              ·
                refine ⟨9029141199806035477709591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019427466537356985139727 9029141199806035477709591)
                ·
                  refine ⟨13543711799709053216564387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9029141199806035477709591 13543711799709053216564387)
                  ·
                    refine ⟨20315567699563579824846581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13543711799709053216564387 20315567699563579824846581)
                    ·
                      refine ⟨1904584471834085608579367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20315567699563579824846581 1904584471834085608579367)
                      ·
                        rfl

theorem cell23_3709165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_3709165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709165 prefixEnd_3709165 := by exact prefixLift 3709165
  have htrace : WordTrace (prefixWord ++ tailWord_3709165) baseStart_3709165 baseEnd_3709165 := by
    simpa [prefixWord, tailWord_3709165, baseEnd_3709165] using wordTrace_append hprefix tailTrace_3709165
  have hstable : (prefixWord ++ tailWord_3709165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709165).length < 2 ^ (prefixWord ++ tailWord_3709165).sum := by decide
  have hdescent : baseEnd_3709165 < baseStart_3709165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709178 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_3709178 : Nat := 118140960795 + 3709178 * 2 ^ 59
def prefixEnd_3709178 : Nat := 4983230072969 + 3 ^ 40 * 3709178 * 2
def baseEnd_3709178 : Nat := 1904591147082594057716807

theorem tailTrace_3709178 : CollatzResearch.WordTrace tailWord_3709178 prefixEnd_3709178 1904591147082594057716807 := by
  unfold tailWord_3709178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33821208939072264503454047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90189890504192705342544125 33821208939072264503454047)
  ·
    refine ⟨50731813408608396755181071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33821208939072264503454047 50731813408608396755181071)
    ·
      refine ⟨76097720112912595132771607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50731813408608396755181071 76097720112912595132771607)
      ·
        refine ⟨114146580169368892699157411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76097720112912595132771607 114146580169368892699157411)
        ·
          refine ⟨171219870254053339048736117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114146580169368892699157411 171219870254053339048736117)
          ·
            refine ⟨16051862836317500535819011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171219870254053339048736117 16051862836317500535819011)
            ·
              refine ⟨24077794254476250803728517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16051862836317500535819011 24077794254476250803728517)
              ·
                refine ⟨4514586422714297025699097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24077794254476250803728517 4514586422714297025699097)
                ·
                  refine ⟨3385939817035722769274323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514586422714297025699097 3385939817035722769274323)
                  ·
                    refine ⟨5078909725553584153911485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3385939817035722769274323 5078909725553584153911485)
                    ·
                      refine ⟨1904591147082594057716807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5078909725553584153911485 1904591147082594057716807)
                      ·
                        rfl

theorem cell23_3709178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_3709178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709178 prefixEnd_3709178 := by exact prefixLift 3709178
  have htrace : WordTrace (prefixWord ++ tailWord_3709178) baseStart_3709178 baseEnd_3709178 := by
    simpa [prefixWord, tailWord_3709178, baseEnd_3709178] using wordTrace_append hprefix tailTrace_3709178
  have hstable : (prefixWord ++ tailWord_3709178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709178).length < 2 ^ (prefixWord ++ tailWord_3709178).sum := by decide
  have hdescent : baseEnd_3709178 < baseStart_3709178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709184 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_3709184 : Nat := 118140960795 + 3709184 * 2 ^ 59
def prefixEnd_3709184 : Nat := 4983230072969 + 3 ^ 40 * 3709184 * 2
def baseEnd_3709184 : Nat := 1904594227966521034241779

theorem tailTrace_3709184 : CollatzResearch.WordTrace tailWord_3709184 prefixEnd_3709184 1904594227966521034241779 := by
  unfold tailWord_3709184
  simp only [CollatzResearch.WordTrace]
  refine ⟨67642527297133660519267303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90190036396178214025689737 67642527297133660519267303)
  ·
    refine ⟨101463790945700490778900955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67642527297133660519267303 101463790945700490778900955)
    ·
      refine ⟨152195686418550736168351433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101463790945700490778900955 152195686418550736168351433)
      ·
        refine ⟨114146764813913052126263575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152195686418550736168351433 114146764813913052126263575)
        ·
          refine ⟨171220147220869578189395363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114146764813913052126263575 171220147220869578189395363)
          ·
            refine ⟨256830220831304367284093045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171220147220869578189395363 256830220831304367284093045)
            ·
              refine ⟨24077833202934784432883723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256830220831304367284093045 24077833202934784432883723)
              ·
                refine ⟨36116749804402176649325585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24077833202934784432883723 36116749804402176649325585)
                ·
                  refine ⟨27087562353301632486994189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36116749804402176649325585 27087562353301632486994189)
                  ·
                    refine ⟨10157835882488112182622821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27087562353301632486994189 10157835882488112182622821)
                    ·
                      refine ⟨1904594227966521034241779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10157835882488112182622821 1904594227966521034241779)
                      ·
                        rfl

theorem cell23_3709184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_3709184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709184 prefixEnd_3709184 := by exact prefixLift 3709184
  have htrace : WordTrace (prefixWord ++ tailWord_3709184) baseStart_3709184 baseEnd_3709184 := by
    simpa [prefixWord, tailWord_3709184, baseEnd_3709184] using wordTrace_append hprefix tailTrace_3709184
  have hstable : (prefixWord ++ tailWord_3709184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709184).length < 2 ^ (prefixWord ++ tailWord_3709184).sum := by decide
  have hdescent : baseEnd_3709184 < baseStart_3709184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709194 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_3709194 : Nat := 118140960795 + 3709194 * 2 ^ 59
def prefixEnd_3709194 : Nat := 4983230072969 + 3 ^ 40 * 3709194 * 2
def baseEnd_3709194 : Nat := 634866454257688665038911

theorem tailTrace_3709194 : CollatzResearch.WordTrace tailWord_3709194 prefixEnd_3709194 634866454257688665038911 := by
  unfold tailWord_3709194
  simp only [CollatzResearch.WordTrace]
  refine ⟨33821354831057773186599659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90190279549487395164265757 33821354831057773186599659)
  ·
    refine ⟨50732032246586659779899489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33821354831057773186599659 50732032246586659779899489)
    ·
      refine ⟨38049024184939994834924617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50732032246586659779899489 38049024184939994834924617)
      ·
        refine ⟨28536768138704996126193463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38049024184939994834924617 28536768138704996126193463)
        ·
          refine ⟨42805152208057494189290195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28536768138704996126193463 42805152208057494189290195)
          ·
            refine ⟨64207728312086241283935293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42805152208057494189290195 64207728312086241283935293)
            ·
              refine ⟨24077898117032340481475735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64207728312086241283935293 24077898117032340481475735)
              ·
                refine ⟨36116847175548510722213603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24077898117032340481475735 36116847175548510722213603)
                ·
                  refine ⟨54175270763322766083320405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36116847175548510722213603 54175270763322766083320405)
                  ·
                    refine ⟨634866454257688665038911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54175270763322766083320405 634866454257688665038911)
                    ·
                      rfl

theorem cell23_3709194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_3709194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709194 prefixEnd_3709194 := by exact prefixLift 3709194
  have htrace : WordTrace (prefixWord ++ tailWord_3709194) baseStart_3709194 baseEnd_3709194 := by
    simpa [prefixWord, tailWord_3709194, baseEnd_3709194] using wordTrace_append hprefix tailTrace_3709194
  have hstable : (prefixWord ++ tailWord_3709194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709194).length < 2 ^ (prefixWord ++ tailWord_3709194).sum := by decide
  have hdescent : baseEnd_3709194 < baseStart_3709194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709229 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3709229 : Nat := 118140960795 + 3709229 * 2 ^ 59
def prefixEnd_3709229 : Nat := 4983230072969 + 3 ^ 40 * 3709229 * 2
def baseEnd_3709229 : Nat := 1904617334595973358179073

theorem tailTrace_3709229 : CollatzResearch.WordTrace tailWord_3709229 prefixEnd_3709229 1904617334595973358179073 := by
  unfold tailWord_3709229
  simp only [CollatzResearch.WordTrace]
  refine ⟨135286695879104293723922741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90191130586069529149281827 135286695879104293723922741)
  ·
    refine ⟨12683127738666027536617757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135286695879104293723922741 12683127738666027536617757)
    ·
      refine ⟨4756172901999760326231659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12683127738666027536617757 4756172901999760326231659)
      ·
        refine ⟨7134259352999640489347489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4756172901999760326231659 7134259352999640489347489)
        ·
          refine ⟨5350694514749730367010617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7134259352999640489347489 5350694514749730367010617)
          ·
            refine ⟨4013020886062297775257963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5350694514749730367010617 4013020886062297775257963)
            ·
              refine ⟨6019531329093446662886945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013020886062297775257963 6019531329093446662886945)
              ·
                refine ⟨4514648496820084997165209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6019531329093446662886945 4514648496820084997165209)
                ·
                  refine ⟨3385986372615063747873907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514648496820084997165209 3385986372615063747873907)
                  ·
                    refine ⟨5078979558922595621810861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3385986372615063747873907 5078979558922595621810861)
                    ·
                      refine ⟨1904617334595973358179073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5078979558922595621810861 1904617334595973358179073)
                      ·
                        rfl

theorem cell23_3709229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3709229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709229 prefixEnd_3709229 := by exact prefixLift 3709229
  have htrace : WordTrace (prefixWord ++ tailWord_3709229) baseStart_3709229 baseEnd_3709229 := by
    simpa [prefixWord, tailWord_3709229, baseEnd_3709229] using wordTrace_append hprefix tailTrace_3709229
  have hstable : (prefixWord ++ tailWord_3709229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709229).length < 2 ^ (prefixWord ++ tailWord_3709229).sum := by decide
  have hdescent : baseEnd_3709229 < baseStart_3709229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709241 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 7]
def baseStart_3709241 : Nat := 118140960795 + 3709241 * 2 ^ 59
def prefixEnd_3709241 : Nat := 4983230072969 + 3 ^ 40 * 3709241 * 2
def baseEnd_3709241 : Nat := 211624832929314145692113

theorem tailTrace_3709241 : CollatzResearch.WordTrace tailWord_3709241 prefixEnd_3709241 211624832929314145692113 := by
  unfold tailWord_3709241
  simp only [CollatzResearch.WordTrace]
  refine ⟨135287133555060819773359577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90191422370040546515573051 135287133555060819773359577)
  ·
    refine ⟨101465350166295614830019683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135287133555060819773359577 101465350166295614830019683)
    ·
      refine ⟨152198025249443422245029525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101465350166295614830019683 152198025249443422245029525)
      ·
        refine ⟨7134282433567660417735759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152198025249443422245029525 7134282433567660417735759)
        ·
          refine ⟨10701423650351490626603639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7134282433567660417735759 10701423650351490626603639)
          ·
            refine ⟨16052135475527235939905459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701423650351490626603639 16052135475527235939905459)
            ·
              refine ⟨24078203213290853909858189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16052135475527235939905459 24078203213290853909858189)
              ·
                refine ⟨9029326204984070216196821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24078203213290853909858189 9029326204984070216196821)
                ·
                  refine ⟨211624832929314145692113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9029326204984070216196821 211624832929314145692113)
                  ·
                    rfl

theorem cell23_3709241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_3709241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709241 prefixEnd_3709241 := by exact prefixLift 3709241
  have htrace : WordTrace (prefixWord ++ tailWord_3709241) baseStart_3709241 baseEnd_3709241 := by
    simpa [prefixWord, tailWord_3709241, baseEnd_3709241] using wordTrace_append hprefix tailTrace_3709241
  have hstable : (prefixWord ++ tailWord_3709241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709241).length < 2 ^ (prefixWord ++ tailWord_3709241).sum := by decide
  have hdescent : baseEnd_3709241 < baseStart_3709241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709251 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 3]
def baseStart_3709251 : Nat := 118140960795 + 3709251 * 2 ^ 59
def prefixEnd_3709251 : Nat := 4983230072969 + 3 ^ 40 * 3709251 * 2
def baseEnd_3709251 : Nat := 1904628631170372272103971

theorem tailTrace_3709251 : CollatzResearch.WordTrace tailWord_3709251 prefixEnd_3709251 1904628631170372272103971 := by
  unfold tailWord_3709251
  simp only [CollatzResearch.WordTrace]
  refine ⟨135287498285024591481223607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90191665523349727654149071 135287498285024591481223607)
  ·
    refine ⟨202931247427536887221835411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135287498285024591481223607 202931247427536887221835411)
    ·
      refine ⟨304396871141305330832753117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202931247427536887221835411 304396871141305330832753117)
      ·
        refine ⟨114148826677989499062282419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304396871141305330832753117 114148826677989499062282419)
        ·
          refine ⟨171223240016984248593423629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114148826677989499062282419 171223240016984248593423629)
          ·
            refine ⟨64208715006369093222533861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171223240016984248593423629 64208715006369093222533861)
            ·
              refine ⟨12039134063694204979225099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64208715006369093222533861 12039134063694204979225099)
              ·
                refine ⟨18058701095541307468837649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12039134063694204979225099 18058701095541307468837649)
                ·
                  refine ⟨13544025821655980601628237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18058701095541307468837649 13544025821655980601628237)
                  ·
                    refine ⟨5079009683120992725610589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13544025821655980601628237 5079009683120992725610589)
                    ·
                      refine ⟨1904628631170372272103971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079009683120992725610589 1904628631170372272103971)
                      ·
                        rfl

theorem cell23_3709251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_3709251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709251 prefixEnd_3709251 := by exact prefixLift 3709251
  have htrace : WordTrace (prefixWord ++ tailWord_3709251) baseStart_3709251 baseEnd_3709251 := by
    simpa [prefixWord, tailWord_3709251, baseEnd_3709251] using wordTrace_append hprefix tailTrace_3709251
  have hstable : (prefixWord ++ tailWord_3709251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709251).length < 2 ^ (prefixWord ++ tailWord_3709251).sum := by decide
  have hdescent : baseEnd_3709251 < baseStart_3709251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709271 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 2, 5]
def baseStart_3709271 : Nat := 118140960795 + 3709271 * 2 ^ 59
def prefixEnd_3709271 : Nat := 4983230072969 + 3 ^ 40 * 3709271 * 2
def baseEnd_3709271 : Nat := 634879633594487397951293

theorem tailTrace_3709271 : CollatzResearch.WordTrace tailWord_3709271 prefixEnd_3709271 634879633594487397951293 := by
  unfold tailWord_3709271
  simp only [CollatzResearch.WordTrace]
  refine ⟨135288227744952134896951667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90192151829968089931301111 135288227744952134896951667)
  ·
    refine ⟨202932341617428202345427501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135288227744952134896951667 202932341617428202345427501)
    ·
      refine ⟨76099628106535575879535313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202932341617428202345427501 76099628106535575879535313)
      ·
        refine ⟨57074721079901681909651485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76099628106535575879535313 57074721079901681909651485)
        ·
          refine ⟨21403020404963130716119307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57074721079901681909651485 21403020404963130716119307)
          ·
            refine ⟨32104530607444696074178961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21403020404963130716119307 32104530607444696074178961)
            ·
              refine ⟨24078397955583522055634221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32104530607444696074178961 24078397955583522055634221)
              ·
                refine ⟨9029399233343820770862833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24078397955583522055634221 9029399233343820770862833)
                ·
                  refine ⟨6772049425007865578147125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9029399233343820770862833 6772049425007865578147125)
                  ·
                    refine ⟨634879633594487397951293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6772049425007865578147125 634879633594487397951293)
                    ·
                      rfl

theorem cell23_3709271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_3709271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709271 prefixEnd_3709271 := by exact prefixLift 3709271
  have htrace : WordTrace (prefixWord ++ tailWord_3709271) baseStart_3709271 baseEnd_3709271 := by
    simpa [prefixWord, tailWord_3709271, baseEnd_3709271] using wordTrace_append hprefix tailTrace_3709271
  have hstable : (prefixWord ++ tailWord_3709271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709271).length < 2 ^ (prefixWord ++ tailWord_3709271).sum := by decide
  have hdescent : baseEnd_3709271 < baseStart_3709271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709288 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3709288 : Nat := 118140960795 + 3709288 * 2 ^ 59
def prefixEnd_3709288 : Nat := 4983230072969 + 3 ^ 40 * 3709288 * 2
def baseEnd_3709288 : Nat := 634882543318196209113767

theorem tailTrace_3709288 : CollatzResearch.WordTrace tailWord_3709288 prefixEnd_3709288 634882543318196209113767 := by
  unfold tailWord_3709288
  simp only [CollatzResearch.WordTrace]
  refine ⟨67644423892945273400160259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90192565190593697866880345 67644423892945273400160259)
  ·
    refine ⟨101466635839417910100240389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67644423892945273400160259 101466635839417910100240389)
    ·
      refine ⟨19024994219890858143795073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101466635839417910100240389 19024994219890858143795073)
      ·
        refine ⟨14268745664918143607846305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19024994219890858143795073 14268745664918143607846305)
        ·
          refine ⟨10701559248688607705884729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14268745664918143607846305 10701559248688607705884729)
          ·
            refine ⟨8026169436516455779413547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10701559248688607705884729 8026169436516455779413547)
            ·
              refine ⟨12039254154774683669120321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026169436516455779413547 12039254154774683669120321)
              ·
                refine ⟨9029440616081012751840241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12039254154774683669120321 9029440616081012751840241)
                ·
                  refine ⟨6772080462060759563880181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9029440616081012751840241 6772080462060759563880181)
                  ·
                    refine ⟨634882543318196209113767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6772080462060759563880181 634882543318196209113767)
                    ·
                      rfl

theorem cell23_3709288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3709288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709288 prefixEnd_3709288 := by exact prefixLift 3709288
  have htrace : WordTrace (prefixWord ++ tailWord_3709288) baseStart_3709288 baseEnd_3709288 := by
    simpa [prefixWord, tailWord_3709288, baseEnd_3709288] using wordTrace_append hprefix tailTrace_3709288
  have hstable : (prefixWord ++ tailWord_3709288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709288).length < 2 ^ (prefixWord ++ tailWord_3709288).sum := by decide
  have hdescent : baseEnd_3709288 < baseStart_3709288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709291 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 4]
def baseStart_3709291 : Nat := 118140960795 + 3709291 * 2 ^ 59
def prefixEnd_3709291 : Nat := 4983230072969 + 3 ^ 40 * 3709291 * 2
def baseEnd_3709291 : Nat := 1904649170396552115603787

theorem tailTrace_3709291 : CollatzResearch.WordTrace tailWord_3709291 prefixEnd_3709291 1904649170396552115603787 := by
  unfold tailWord_3709291
  simp only [CollatzResearch.WordTrace]
  refine ⟨135288957204879678312679727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90192638136586452208453151 135288957204879678312679727)
  ·
    refine ⟨202933435807319517469019591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135288957204879678312679727 202933435807319517469019591)
    ·
      refine ⟨304400153710979276203529387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202933435807319517469019591 304400153710979276203529387)
      ·
        refine ⟨456600230566468914305294081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304400153710979276203529387 456600230566468914305294081)
        ·
          refine ⟨342450172924851685728970561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456600230566468914305294081 342450172924851685728970561)
          ·
            refine ⟨256837629693638764296727921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342450172924851685728970561 256837629693638764296727921)
            ·
              refine ⟨192628222270229073222545941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256837629693638764296727921 192628222270229073222545941)
              ·
                refine ⟨9029447918916987807306841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192628222270229073222545941 9029447918916987807306841)
                ·
                  refine ⟨6772085939187740855480131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9029447918916987807306841 6772085939187740855480131)
                  ·
                    refine ⟨10158128908781611283220197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6772085939187740855480131 10158128908781611283220197)
                    ·
                      refine ⟨1904649170396552115603787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10158128908781611283220197 1904649170396552115603787)
                      ·
                        rfl

theorem cell23_3709291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 4].length) (baseStart_3709291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709291 prefixEnd_3709291 := by exact prefixLift 3709291
  have htrace : WordTrace (prefixWord ++ tailWord_3709291) baseStart_3709291 baseEnd_3709291 := by
    simpa [prefixWord, tailWord_3709291, baseEnd_3709291] using wordTrace_append hprefix tailTrace_3709291
  have hstable : (prefixWord ++ tailWord_3709291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709291).length < 2 ^ (prefixWord ++ tailWord_3709291).sum := by decide
  have hdescent : baseEnd_3709291 < baseStart_3709291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709368 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 1, 5, 2]
def baseStart_3709368 : Nat := 118140960795 + 3709368 * 2 ^ 59
def prefixEnd_3709368 : Nat := 4983230072969 + 3 ^ 40 * 3709368 * 2
def baseEnd_3709368 : Nat := 1904688708406948314340933

theorem tailTrace_3709368 : CollatzResearch.WordTrace tailWord_3709368 prefixEnd_3709368 1904688708406948314340933 := by
  unfold tailWord_3709368
  simp only [CollatzResearch.WordTrace]
  refine ⟨67645882812800360231616379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90194510417067146975488505 67645882812800360231616379)
  ·
    refine ⟨101468824219200540347424569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67645882812800360231616379 101468824219200540347424569)
    ·
      refine ⟨76101618164400405260568427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101468824219200540347424569 76101618164400405260568427)
      ·
        refine ⟨114152427246600607890852641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76101618164400405260568427 114152427246600607890852641)
        ·
          refine ⟨85614320434950455918139481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114152427246600607890852641 85614320434950455918139481)
          ·
            refine ⟨64210740326212841938604611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85614320434950455918139481 64210740326212841938604611)
            ·
              refine ⟨96316110489319262907906917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64210740326212841938604611 96316110489319262907906917)
              ·
                refine ⟨18059270716747361795232547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96316110489319262907906917 18059270716747361795232547)
                ·
                  refine ⟨27088906075121042692848821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18059270716747361795232547 27088906075121042692848821)
                  ·
                    refine ⟨2539584944542597752454577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27088906075121042692848821 2539584944542597752454577)
                    ·
                      refine ⟨1904688708406948314340933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2539584944542597752454577 1904688708406948314340933)
                      ·
                        rfl

theorem cell23_3709368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_3709368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709368 prefixEnd_3709368 := by exact prefixLift 3709368
  have htrace : WordTrace (prefixWord ++ tailWord_3709368) baseStart_3709368 baseEnd_3709368 := by
    simpa [prefixWord, tailWord_3709368, baseEnd_3709368] using wordTrace_append hprefix tailTrace_3709368
  have hstable : (prefixWord ++ tailWord_3709368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709368).length < 2 ^ (prefixWord ++ tailWord_3709368).sum := by decide
  have hdescent : baseEnd_3709368 < baseStart_3709368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709385 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 2, 3, 2]
def baseStart_3709385 : Nat := 118140960795 + 3709385 * 2 ^ 59
def prefixEnd_3709385 : Nat := 4983230072969 + 3 ^ 40 * 3709385 * 2
def baseEnd_3709385 : Nat := 1904697437578074747828355

theorem tailTrace_3709385 : CollatzResearch.WordTrace tailWord_3709385 prefixEnd_3709385 1904697437578074747828355 := by
  unfold tailWord_3709385
  simp only [CollatzResearch.WordTrace]
  refine ⟨135292385666539132366601609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90194923777692754911067739 135292385666539132366601609)
  ·
    refine ⟨101469289249904349274951207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135292385666539132366601609 101469289249904349274951207)
    ·
      refine ⟨152203933874856523912426811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101469289249904349274951207 152203933874856523912426811)
      ·
        refine ⟨228305900812284785868640217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152203933874856523912426811 228305900812284785868640217)
        ·
          refine ⟨171229425609213589401480163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228305900812284785868640217 171229425609213589401480163)
          ·
            refine ⟨256844138413820384102220245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171229425609213589401480163 256844138413820384102220245)
            ·
              refine ⟨6019784494073915252395787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 256844138413820384102220245 6019784494073915252395787)
              ·
                refine ⟨9029676741110872878593681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019784494073915252395787 9029676741110872878593681)
                ·
                  refine ⟨6772257555833154658945261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9029676741110872878593681 6772257555833154658945261)
                  ·
                    refine ⟨2539596583437432997104473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6772257555833154658945261 2539596583437432997104473)
                    ·
                      refine ⟨1904697437578074747828355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2539596583437432997104473 1904697437578074747828355)
                      ·
                        rfl

theorem cell23_3709385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 3, 2].length) (baseStart_3709385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709385 prefixEnd_3709385 := by exact prefixLift 3709385
  have htrace : WordTrace (prefixWord ++ tailWord_3709385) baseStart_3709385 baseEnd_3709385 := by
    simpa [prefixWord, tailWord_3709385, baseEnd_3709385] using wordTrace_append hprefix tailTrace_3709385
  have hstable : (prefixWord ++ tailWord_3709385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709385).length < 2 ^ (prefixWord ++ tailWord_3709385).sum := by decide
  have hdescent : baseEnd_3709385 < baseStart_3709385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709408 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 4, 4]
def baseStart_3709408 : Nat := 118140960795 + 3709408 * 2 ^ 59
def prefixEnd_3709408 : Nat := 4983230072969 + 3 ^ 40 * 3709408 * 2
def baseEnd_3709408 : Nat := 634903082544376052613583

theorem tailTrace_3709408 : CollatzResearch.WordTrace tailWord_3709408 prefixEnd_3709408 634903082544376052613583 := by
  unfold tailWord_3709408
  simp only [CollatzResearch.WordTrace]
  refine ⟨67646612272727903647344439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90195483030303871529792585 67646612272727903647344439)
  ·
    refine ⟨101469918409091855471016659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67646612272727903647344439 101469918409091855471016659)
    ·
      refine ⟨152204877613637783206524989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101469918409091855471016659 152204877613637783206524989)
      ·
        refine ⟨57076829105114168702446871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152204877613637783206524989 57076829105114168702446871)
        ·
          refine ⟨85615243657671253053670307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57076829105114168702446871 85615243657671253053670307)
          ·
            refine ⟨128422865486506879580505461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85615243657671253053670307 128422865486506879580505461)
            ·
              refine ⟨12039643639360019960672387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128422865486506879580505461 12039643639360019960672387)
              ·
                refine ⟨18059465459040029941008581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12039643639360019960672387 18059465459040029941008581)
                ·
                  refine ⟨3386149773570005613939109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18059465459040029941008581 3386149773570005613939109)
                  ·
                    refine ⟨634903082544376052613583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3386149773570005613939109 634903082544376052613583)
                    ·
                      rfl

theorem cell23_3709408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_3709408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709408 prefixEnd_3709408 := by exact prefixLift 3709408
  have htrace : WordTrace (prefixWord ++ tailWord_3709408) baseStart_3709408 baseEnd_3709408 := by
    simpa [prefixWord, tailWord_3709408, baseEnd_3709408] using wordTrace_append hprefix tailTrace_3709408
  have hstable : (prefixWord ++ tailWord_3709408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709408).length < 2 ^ (prefixWord ++ tailWord_3709408).sum := by decide
  have hdescent : baseEnd_3709408 < baseStart_3709408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709418 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3709418 : Nat := 118140960795 + 3709418 * 2 ^ 59
def prefixEnd_3709418 : Nat := 4983230072969 + 3 ^ 40 * 3709418 * 2
def baseEnd_3709418 : Nat := 1904714382439673118715703

theorem tailTrace_3709418 : CollatzResearch.WordTrace tailWord_3709418 prefixEnd_3709418 1904714382439673118715703 := by
  unfold tailWord_3709418
  simp only [CollatzResearch.WordTrace]
  refine ⟨33823397318854894750638227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90195726183613052668368605 33823397318854894750638227)
  ·
    refine ⟨50735095978282342125957341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33823397318854894750638227 50735095978282342125957341)
    ·
      refine ⟨19025660991855878297234003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50735095978282342125957341 19025660991855878297234003)
      ·
        refine ⟨28538491487783817445851005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19025660991855878297234003 28538491487783817445851005)
        ·
          refine ⟨10701934307918931542194127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28538491487783817445851005 10701934307918931542194127)
          ·
            refine ⟨16052901461878397313291191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701934307918931542194127 16052901461878397313291191)
            ·
              refine ⟨24079352192817595969936787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16052901461878397313291191 24079352192817595969936787)
              ·
                refine ⟨36119028289226393954905181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24079352192817595969936787 36119028289226393954905181)
                ·
                  refine ⟨13544635608459897733089443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36119028289226393954905181 13544635608459897733089443)
                  ·
                    refine ⟨20316953412689846599634165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13544635608459897733089443 20316953412689846599634165)
                    ·
                      refine ⟨1904714382439673118715703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20316953412689846599634165 1904714382439673118715703)
                      ·
                        rfl

theorem cell23_3709418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3709418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709418 prefixEnd_3709418 := by exact prefixLift 3709418
  have htrace : WordTrace (prefixWord ++ tailWord_3709418) baseStart_3709418 baseEnd_3709418 := by
    simpa [prefixWord, tailWord_3709418, baseEnd_3709418] using wordTrace_append hprefix tailTrace_3709418
  have hstable : (prefixWord ++ tailWord_3709418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709418).length < 2 ^ (prefixWord ++ tailWord_3709418).sum := by decide
  have hdescent : baseEnd_3709418 < baseStart_3709418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709448 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3709448 : Nat := 118140960795 + 3709448 * 2 ^ 59
def prefixEnd_3709448 : Nat := 4983230072969 + 3 ^ 40 * 3709448 * 2
def baseEnd_3709448 : Nat := 1904729786859308001340565

theorem tailTrace_3709448 : CollatzResearch.WordTrace tailWord_3709448 prefixEnd_3709448 1904729786859308001340565 := by
  unfold tailWord_3709448
  simp only [CollatzResearch.WordTrace]
  refine ⟨67647341732655447063072499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90196455643540596084096665 67647341732655447063072499)
  ·
    refine ⟨101471012598983170594608749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67647341732655447063072499 101471012598983170594608749)
    ·
      refine ⟨38051629724618688972978281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101471012598983170594608749 38051629724618688972978281)
      ·
        refine ⟨28538722293464016729733711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38051629724618688972978281 28538722293464016729733711)
        ·
          refine ⟨42808083440196025094600567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28538722293464016729733711 42808083440196025094600567)
          ·
            refine ⟨64212125160294037641900851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42808083440196025094600567 64212125160294037641900851)
            ·
              refine ⟨96318187740441056462851277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64212125160294037641900851 96318187740441056462851277)
              ·
                refine ⟨36119320402665396173569229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96318187740441056462851277 36119320402665396173569229)
                ·
                  refine ⟨13544745150999523565088461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36119320402665396173569229 13544745150999523565088461)
                  ·
                    refine ⟨5079279431624821336908173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13544745150999523565088461 5079279431624821336908173)
                    ·
                      refine ⟨1904729786859308001340565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079279431624821336908173 1904729786859308001340565)
                      ·
                        rfl

theorem cell23_3709448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3709448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709448 prefixEnd_3709448 := by exact prefixLift 3709448
  have htrace : WordTrace (prefixWord ++ tailWord_3709448) baseStart_3709448 baseEnd_3709448 := by
    simpa [prefixWord, tailWord_3709448, baseEnd_3709448] using wordTrace_append hprefix tailTrace_3709448
  have hstable : (prefixWord ++ tailWord_3709448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709448).length < 2 ^ (prefixWord ++ tailWord_3709448).sum := by decide
  have hdescent : baseEnd_3709448 < baseStart_3709448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709476 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_3709476 : Nat := 118140960795 + 3709476 * 2 ^ 59
def prefixEnd_3709476 : Nat := 4983230072969 + 3 ^ 40 * 3709476 * 2
def baseEnd_3709476 : Nat := 634914721439211297263479

theorem tailTrace_3709476 : CollatzResearch.WordTrace tailWord_3709476 prefixEnd_3709476 634914721439211297263479 := by
  unfold tailWord_3709476
  simp only [CollatzResearch.WordTrace]
  refine ⟨67647852354604727454082141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90197136472806303272109521 67647852354604727454082141)
  ·
    refine ⟨25367944632976772795280803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67647852354604727454082141 25367944632976772795280803)
    ·
      refine ⟨38051916949465159192921205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25367944632976772795280803 38051916949465159192921205)
      ·
        refine ⟨3567367214012358674336363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38051916949465159192921205 3567367214012358674336363)
        ·
          refine ⟨5351050821018538011504545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567367214012358674336363 5351050821018538011504545)
          ·
            refine ⟨4013288115763903508628409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5351050821018538011504545 4013288115763903508628409)
            ·
              refine ⟨3009966086822927631471307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4013288115763903508628409 3009966086822927631471307)
              ·
                refine ⟨4514949130234391447206961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009966086822927631471307 4514949130234391447206961)
                ·
                  refine ⟨3386211847675793585405221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514949130234391447206961 3386211847675793585405221)
                  ·
                    refine ⟨634914721439211297263479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3386211847675793585405221 634914721439211297263479)
                    ·
                      rfl

theorem cell23_3709476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_3709476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709476 prefixEnd_3709476 := by exact prefixLift 3709476
  have htrace : WordTrace (prefixWord ++ tailWord_3709476) baseStart_3709476 baseEnd_3709476 := by
    simpa [prefixWord, tailWord_3709476, baseEnd_3709476] using wordTrace_append hprefix tailTrace_3709476
  have hstable : (prefixWord ++ tailWord_3709476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709476).length < 2 ^ (prefixWord ++ tailWord_3709476).sum := by decide
  have hdescent : baseEnd_3709476 < baseStart_3709476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709486 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_3709486 : Nat := 118140960795 + 3709486 * 2 ^ 59
def prefixEnd_3709486 : Nat := 4983230072969 + 3 ^ 40 * 3709486 * 2
def baseEnd_3709486 : Nat := 1904749299124178852665391

theorem tailTrace_3709486 : CollatzResearch.WordTrace tailWord_3709486 prefixEnd_3709486 1904749299124178852665391 := by
  unfold tailWord_3709486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16912008679896653327003539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90197379626115484410685541 16912008679896653327003539)
  ·
    refine ⟨25368013019844979990505309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16912008679896653327003539 25368013019844979990505309)
    ·
      refine ⟨9513004882441867496439491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25368013019844979990505309 9513004882441867496439491)
      ·
        refine ⟨14269507323662801244659237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9513004882441867496439491 14269507323662801244659237)
        ·
          refine ⟨2675532623186775233373607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14269507323662801244659237 2675532623186775233373607)
          ·
            refine ⟨4013298934780162850060411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675532623186775233373607 4013298934780162850060411)
            ·
              refine ⟨6019948402170244275090617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013298934780162850060411 6019948402170244275090617)
              ·
                refine ⟨4514961301627683206317963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6019948402170244275090617 4514961301627683206317963)
                ·
                  refine ⟨6772441952441524809476945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514961301627683206317963 6772441952441524809476945)
                  ·
                    refine ⟨5079331464331143607107709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6772441952441524809476945 5079331464331143607107709)
                    ·
                      refine ⟨1904749299124178852665391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079331464331143607107709 1904749299124178852665391)
                      ·
                        rfl

theorem cell23_3709486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_3709486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709486 prefixEnd_3709486 := by exact prefixLift 3709486
  have htrace : WordTrace (prefixWord ++ tailWord_3709486) baseStart_3709486 baseEnd_3709486 := by
    simpa [prefixWord, tailWord_3709486, baseEnd_3709486] using wordTrace_append hprefix tailTrace_3709486
  have hstable : (prefixWord ++ tailWord_3709486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709486).length < 2 ^ (prefixWord ++ tailWord_3709486).sum := by decide
  have hdescent : baseEnd_3709486 < baseStart_3709486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709509 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 1, 3, 2]
def baseStart_3709509 : Nat := 118140960795 + 3709509 * 2 ^ 59
def prefixEnd_3709509 : Nat := 4983230072969 + 3 ^ 40 * 3709509 * 2
def baseEnd_3709509 : Nat := 1904761109179232262677785

theorem tailTrace_3709509 : CollatzResearch.WordTrace tailWord_3709509 prefixEnd_3709509 1904761109179232262677785 := by
  unfold tailWord_3709509
  simp only [CollatzResearch.WordTrace]
  refine ⟨135296908318089901544115581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90197938878726601029410387 135296908318089901544115581)
  ·
    refine ⟨50736340619283713079043343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135296908318089901544115581 50736340619283713079043343)
    ·
      refine ⟨76104510928925569618565015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50736340619283713079043343 76104510928925569618565015)
      ·
        refine ⟨114156766393388354427847523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76104510928925569618565015 114156766393388354427847523)
        ·
          refine ⟨171235149590082531641771285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114156766393388354427847523 171235149590082531641771285)
          ·
            refine ⟨8026647637035118670708029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171235149590082531641771285 8026647637035118670708029)
            ·
              refine ⟨3009992863888169501515511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8026647637035118670708029 3009992863888169501515511)
              ·
                refine ⟨4514989295832254252273267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009992863888169501515511 4514989295832254252273267)
                ·
                  refine ⟨6772483943748381378409901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514989295832254252273267 6772483943748381378409901)
                  ·
                    refine ⟨2539681478905643016903713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6772483943748381378409901 2539681478905643016903713)
                    ·
                      refine ⟨1904761109179232262677785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2539681478905643016903713 1904761109179232262677785)
                      ·
                        rfl

theorem cell23_3709509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_3709509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709509 prefixEnd_3709509 := by exact prefixLift 3709509
  have htrace : WordTrace (prefixWord ++ tailWord_3709509) baseStart_3709509 baseEnd_3709509 := by
    simpa [prefixWord, tailWord_3709509, baseEnd_3709509] using wordTrace_append hprefix tailTrace_3709509
  have hstable : (prefixWord ++ tailWord_3709509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709509).length < 2 ^ (prefixWord ++ tailWord_3709509).sum := by decide
  have hdescent : baseEnd_3709509 < baseStart_3709509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709615 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 3]
def baseStart_3709615 : Nat := 118140960795 + 3709615 * 2 ^ 59
def prefixEnd_3709615 : Nat := 4983230072969 + 3 ^ 40 * 3709615 * 2
def baseEnd_3709615 : Nat := 1904815538128608847952297

theorem tailTrace_3709615 : CollatzResearch.WordTrace tailWord_3709615 prefixEnd_3709615 1904815538128608847952297 := by
  unfold tailWord_3709615
  simp only [CollatzResearch.WordTrace]
  refine ⟨135300774455705881647474299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90200516303803921098316199 135300774455705881647474299)
  ·
    refine ⟨202951161683558822471211449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135300774455705881647474299 202951161683558822471211449)
    ·
      refine ⟨152213371262669116853408587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202951161683558822471211449 152213371262669116853408587)
      ·
        refine ⟨228320056894003675280112881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152213371262669116853408587 228320056894003675280112881)
        ·
          refine ⟨171240042670502756460084661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228320056894003675280112881 171240042670502756460084661)
          ·
            refine ⟨16053754000359633418132937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171240042670502756460084661 16053754000359633418132937)
            ·
              refine ⟨12040315500269725063599703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16053754000359633418132937 12040315500269725063599703)
              ·
                refine ⟨18060473250404587595399555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12040315500269725063599703 18060473250404587595399555)
                ·
                  refine ⟨27090709875606881393099333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18060473250404587595399555 27090709875606881393099333)
                  ·
                    refine ⟨5079508101676290261206125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27090709875606881393099333 5079508101676290261206125)
                    ·
                      refine ⟨1904815538128608847952297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079508101676290261206125 1904815538128608847952297)
                      ·
                        rfl

theorem cell23_3709615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_3709615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709615 prefixEnd_3709615 := by exact prefixLift 3709615
  have htrace : WordTrace (prefixWord ++ tailWord_3709615) baseStart_3709615 baseEnd_3709615 := by
    simpa [prefixWord, tailWord_3709615, baseEnd_3709615] using wordTrace_append hprefix tailTrace_3709615
  have hstable : (prefixWord ++ tailWord_3709615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709615).length < 2 ^ (prefixWord ++ tailWord_3709615).sum := by decide
  have hdescent : baseEnd_3709615 < baseStart_3709615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709632 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3]
def baseStart_3709632 : Nat := 118140960795 + 3709632 * 2 ^ 59
def prefixEnd_3709632 : Nat := 4983230072969 + 3 ^ 40 * 3709632 * 2
def baseEnd_3709632 : Nat := 1904824267299735281439719

theorem tailTrace_3709632 : CollatzResearch.WordTrace tailWord_3709632 prefixEnd_3709632 1904824267299735281439719 := by
  unfold tailWord_3709632
  simp only [CollatzResearch.WordTrace]
  refine ⟨67650697248322146775421575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90200929664429529033895433 67650697248322146775421575)
  ·
    refine ⟨101476045872483220163132363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67650697248322146775421575 101476045872483220163132363)
    ·
      refine ⟨152214068808724830244698545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101476045872483220163132363 152214068808724830244698545)
      ·
        refine ⟨114160551606543622683523909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152214068808724830244698545 114160551606543622683523909)
        ·
          refine ⟨21405103426226929253160733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114160551606543622683523909 21405103426226929253160733)
          ·
            refine ⟨8026913784835098469935275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21405103426226929253160733 8026913784835098469935275)
            ·
              refine ⟨12040370677252647704902913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026913784835098469935275 12040370677252647704902913)
              ·
                refine ⟨9030278007939485778677185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12040370677252647704902913 9030278007939485778677185)
                ·
                  refine ⟨6772708505954614334007889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9030278007939485778677185 6772708505954614334007889)
                  ·
                    refine ⟨5079531379465960750505917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6772708505954614334007889 5079531379465960750505917)
                    ·
                      refine ⟨1904824267299735281439719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079531379465960750505917 1904824267299735281439719)
                      ·
                        rfl

theorem cell23_3709632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_3709632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709632 prefixEnd_3709632 := by exact prefixLift 3709632
  have htrace : WordTrace (prefixWord ++ tailWord_3709632) baseStart_3709632 baseEnd_3709632 := by
    simpa [prefixWord, tailWord_3709632, baseEnd_3709632] using wordTrace_append hprefix tailTrace_3709632
  have hstable : (prefixWord ++ tailWord_3709632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709632).length < 2 ^ (prefixWord ++ tailWord_3709632).sum := by decide
  have hdescent : baseEnd_3709632 < baseStart_3709632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709705 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_3709705 : Nat := 118140960795 + 3709705 * 2 ^ 59
def prefixEnd_3709705 : Nat := 4983230072969 + 3 ^ 40 * 3709705 * 2
def baseEnd_3709705 : Nat := 1904861751387513495826883

theorem tailTrace_3709705 : CollatzResearch.WordTrace tailWord_3709705 prefixEnd_3709705 1904861751387513495826883 := by
  unfold tailWord_3709705
  simp only [CollatzResearch.WordTrace]
  refine ⟨135304057025379827018250569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90202704683586551345500379 135304057025379827018250569)
  ·
    refine ⟨101478042769034870263687927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135304057025379827018250569 101478042769034870263687927)
    ·
      refine ⟨152217064153552305395531891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101478042769034870263687927 152217064153552305395531891)
      ·
        refine ⟨228325596230328458093297837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152217064153552305395531891 228325596230328458093297837)
        ·
          refine ⟨85622098586373171784986689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228325596230328458093297837 85622098586373171784986689)
          ·
            refine ⟨64216573939779878838740017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85622098586373171784986689 64216573939779878838740017)
            ·
              refine ⟨48162430454834909129055013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64216573939779878838740017 48162430454834909129055013)
              ·
                refine ⟨9030455710281545461697815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48162430454834909129055013 9030455710281545461697815)
                ·
                  refine ⟨13545683565422318192546723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9030455710281545461697815 13545683565422318192546723)
                  ·
                    refine ⟨20318525348133477288820085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13545683565422318192546723 20318525348133477288820085)
                    ·
                      refine ⟨1904861751387513495826883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20318525348133477288820085 1904861751387513495826883)
                      ·
                        rfl

theorem cell23_3709705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_3709705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709705 prefixEnd_3709705 := by exact prefixLift 3709705
  have htrace : WordTrace (prefixWord ++ tailWord_3709705) baseStart_3709705 baseEnd_3709705 := by
    simpa [prefixWord, tailWord_3709705, baseEnd_3709705] using wordTrace_append hprefix tailTrace_3709705
  have hstable : (prefixWord ++ tailWord_3709705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709705).length < 2 ^ (prefixWord ++ tailWord_3709705).sum := by decide
  have hdescent : baseEnd_3709705 < baseStart_3709705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709722 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_3709722 : Nat := 118140960795 + 3709722 * 2 ^ 59
def prefixEnd_3709722 : Nat := 4983230072969 + 3 ^ 40 * 3709722 * 2
def baseEnd_3709722 : Nat := 1904870480558639929314305

theorem tailTrace_3709722 : CollatzResearch.WordTrace tailWord_3709722 prefixEnd_3709722 1904870480558639929314305 := by
  unfold tailWord_3709722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33826169266579559730404855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90203118044212159281079613 33826169266579559730404855)
  ·
    refine ⟨50739253899869339595607283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33826169266579559730404855 50739253899869339595607283)
    ·
      refine ⟨76108880849804009393410925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50739253899869339595607283 76108880849804009393410925)
      ·
        refine ⟨28540830318676503522529097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76108880849804009393410925 28540830318676503522529097)
        ·
          refine ⟨21405622739007377641896823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28540830318676503522529097 21405622739007377641896823)
          ·
            refine ⟨32108434108511066462845235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21405622739007377641896823 32108434108511066462845235)
            ·
              refine ⟨48162651162766599694267853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32108434108511066462845235 48162651162766599694267853)
              ·
                refine ⟨18060994186037474885350445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48162651162766599694267853 18060994186037474885350445)
                ·
                  refine ⟨6772872819764053082006417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18060994186037474885350445 6772872819764053082006417)
                  ·
                    refine ⟨5079654614823039811504813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6772872819764053082006417 5079654614823039811504813)
                    ·
                      refine ⟨1904870480558639929314305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079654614823039811504813 1904870480558639929314305)
                      ·
                        rfl

theorem cell23_3709722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_3709722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709722 prefixEnd_3709722 := by exact prefixLift 3709722
  have htrace : WordTrace (prefixWord ++ tailWord_3709722) baseStart_3709722 baseEnd_3709722 := by
    simpa [prefixWord, tailWord_3709722, baseEnd_3709722] using wordTrace_append hprefix tailTrace_3709722
  have hstable : (prefixWord ++ tailWord_3709722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709722).length < 2 ^ (prefixWord ++ tailWord_3709722).sum := by decide
  have hdescent : baseEnd_3709722 < baseStart_3709722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709742 : List Nat := [4, 1, 3, 2, 1, 2, 10]
def baseStart_3709742 : Nat := 118140960795 + 3709742 * 2 ^ 59
def prefixEnd_3709742 : Nat := 4983230072969 + 3 ^ 40 * 3709742 * 2
def baseEnd_3709742 : Nat := 23517046298416417914373

theorem tailTrace_3709742 : CollatzResearch.WordTrace tailWord_3709742 prefixEnd_3709742 23517046298416417914373 := by
  unfold tailWord_3709742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16913175815780722792168435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90203604350830521558231653 16913175815780722792168435)
  ·
    refine ⟨25369763723671084188252653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16913175815780722792168435 25369763723671084188252653)
    ·
      refine ⟨9513661396376656570594745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25369763723671084188252653 9513661396376656570594745)
      ·
        refine ⟨7135246047282492427946059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9513661396376656570594745 7135246047282492427946059)
        ·
          refine ⟨10702869070923738641919089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135246047282492427946059 10702869070923738641919089)
          ·
            refine ⟨8027151803192803981439317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10702869070923738641919089 8027151803192803981439317)
            ·
              refine ⟨23517046298416417914373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8027151803192803981439317 23517046298416417914373)
              ·
                rfl

theorem cell23_3709742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 10].length) (baseStart_3709742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709742 prefixEnd_3709742 := by exact prefixLift 3709742
  have htrace : WordTrace (prefixWord ++ tailWord_3709742) baseStart_3709742 baseEnd_3709742 := by
    simpa [prefixWord, tailWord_3709742, baseEnd_3709742] using wordTrace_append hprefix tailTrace_3709742
  have hstable : (prefixWord ++ tailWord_3709742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709742).length < 2 ^ (prefixWord ++ tailWord_3709742).sum := by decide
  have hdescent : baseEnd_3709742 < baseStart_3709742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709766 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3709766 : Nat := 118140960795 + 3709766 * 2 ^ 59
def prefixEnd_3709766 : Nat := 4983230072969 + 3 ^ 40 * 3709766 * 2
def baseEnd_3709766 : Nat := 1904893073707437757164103

theorem tailTrace_3709766 : CollatzResearch.WordTrace tailWord_3709766 prefixEnd_3709766 1904893073707437757164103 := by
  unfold tailWord_3709766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228321308692463576131911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90204187918772556290814101 4228321308692463576131911)
  ·
    refine ⟨6342481963038695364197867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4228321308692463576131911 6342481963038695364197867)
    ·
      refine ⟨9513722944558043046296801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342481963038695364197867 9513722944558043046296801)
      ·
        refine ⟨7135292208418532284722601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9513722944558043046296801 7135292208418532284722601)
        ·
          refine ⟨5351469156313899213541951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7135292208418532284722601 5351469156313899213541951)
          ·
            refine ⟨8027203734470848820312927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351469156313899213541951 8027203734470848820312927)
            ·
              refine ⟨12040805601706273230469391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8027203734470848820312927 12040805601706273230469391)
              ·
                refine ⟨18061208402559409845704087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12040805601706273230469391 18061208402559409845704087)
                ·
                  refine ⟨27091812603839114768556131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18061208402559409845704087 27091812603839114768556131)
                  ·
                    refine ⟨40637718905758672152834197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27091812603839114768556131 40637718905758672152834197)
                    ·
                      refine ⟨1904893073707437757164103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40637718905758672152834197 1904893073707437757164103)
                      ·
                        rfl

theorem cell23_3709766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3709766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709766 prefixEnd_3709766 := by exact prefixLift 3709766
  have htrace : WordTrace (prefixWord ++ tailWord_3709766) baseStart_3709766 baseEnd_3709766 := by
    simpa [prefixWord, tailWord_3709766, baseEnd_3709766] using wordTrace_append hprefix tailTrace_3709766
  have hstable : (prefixWord ++ tailWord_3709766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709766).length < 2 ^ (prefixWord ++ tailWord_3709766).sum := by decide
  have hdescent : baseEnd_3709766 < baseStart_3709766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709769 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 3]
def baseStart_3709769 : Nat := 118140960795 + 3709769 * 2 ^ 59
def prefixEnd_3709769 : Nat := 4983230072969 + 3 ^ 40 * 3709769 * 2
def baseEnd_3709769 : Nat := 1904894614149401245426589

theorem tailTrace_3709769 : CollatzResearch.WordTrace tailWord_3709769 prefixEnd_3709769 1904894614149401245426589 := by
  unfold tailWord_3709769
  simp only [CollatzResearch.WordTrace]
  refine ⟨135306391297147965948580361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90204260864765310632386907 135306391297147965948580361)
  ·
    refine ⟨101479793472860974461435271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135306391297147965948580361 101479793472860974461435271)
    ·
      refine ⟨152219690209291461692152907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101479793472860974461435271 152219690209291461692152907)
      ·
        refine ⟨228329535313937192538229361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152219690209291461692152907 228329535313937192538229361)
        ·
          refine ⟨171247151485452894403672021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228329535313937192538229361 171247151485452894403672021)
          ·
            refine ⟨4013605112940302212586063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 171247151485452894403672021 4013605112940302212586063)
            ·
              refine ⟨6020407669410453318879095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013605112940302212586063 6020407669410453318879095)
              ·
                refine ⟨9030611504115679978318643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020407669410453318879095 9030611504115679978318643)
                ·
                  refine ⟨13545917256173519967477965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9030611504115679978318643 13545917256173519967477965)
                  ·
                    refine ⟨5079718971065069987804237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13545917256173519967477965 5079718971065069987804237)
                    ·
                      refine ⟨1904894614149401245426589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079718971065069987804237 1904894614149401245426589)
                      ·
                        rfl

theorem cell23_3709769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_3709769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709769 prefixEnd_3709769 := by exact prefixLift 3709769
  have htrace : WordTrace (prefixWord ++ tailWord_3709769) baseStart_3709769 baseEnd_3709769 := by
    simpa [prefixWord, tailWord_3709769, baseEnd_3709769] using wordTrace_append hprefix tailTrace_3709769
  have hstable : (prefixWord ++ tailWord_3709769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709769).length < 2 ^ (prefixWord ++ tailWord_3709769).sum := by decide
  have hdescent : baseEnd_3709769 < baseStart_3709769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709773 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3709773 : Nat := 118140960795 + 3709773 * 2 ^ 59
def prefixEnd_3709773 : Nat := 4983230072969 + 3 ^ 40 * 3709773 * 2
def baseEnd_3709773 : Nat := 1904896668072019229776571

theorem tailTrace_3709773 : CollatzResearch.WordTrace tailWord_3709773 prefixEnd_3709773 1904896668072019229776571 := by
  unfold tailWord_3709773
  simp only [CollatzResearch.WordTrace]
  refine ⟨135306537189133474631725973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90204358126088983087817315 135306537189133474631725973)
  ·
    refine ⟨6342493930740631623362155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135306537189133474631725973 6342493930740631623362155)
    ·
      refine ⟨9513740896110947435043233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342493930740631623362155 9513740896110947435043233)
      ·
        refine ⟨7135305672083210576282425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9513740896110947435043233 7135305672083210576282425)
        ·
          refine ⟨5351479254062407932211819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7135305672083210576282425 5351479254062407932211819)
          ·
            refine ⟨8027218881093611898317729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351479254062407932211819 8027218881093611898317729)
            ·
              refine ⟨6020414160820208923738297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027218881093611898317729 6020414160820208923738297)
              ·
                refine ⟨4515310620615156692803723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020414160820208923738297 4515310620615156692803723)
                ·
                  refine ⟨6772965930922735039205585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515310620615156692803723 6772965930922735039205585)
                  ·
                    refine ⟨5079724448192051279404189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6772965930922735039205585 5079724448192051279404189)
                    ·
                      refine ⟨1904896668072019229776571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079724448192051279404189 1904896668072019229776571)
                      ·
                        rfl

theorem cell23_3709773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3709773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709773 prefixEnd_3709773 := by exact prefixLift 3709773
  have htrace : WordTrace (prefixWord ++ tailWord_3709773) baseStart_3709773 baseEnd_3709773 := by
    simpa [prefixWord, tailWord_3709773, baseEnd_3709773] using wordTrace_append hprefix tailTrace_3709773
  have hstable : (prefixWord ++ tailWord_3709773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709773).length < 2 ^ (prefixWord ++ tailWord_3709773).sum := by decide
  have hdescent : baseEnd_3709773 < baseStart_3709773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709796 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_3709796 : Nat := 118140960795 + 3709796 * 2 ^ 59
def prefixEnd_3709796 : Nat := 4983230072969 + 3 ^ 40 * 3709796 * 2
def baseEnd_3709796 : Nat := 1904908478127072639788965

theorem tailTrace_3709796 : CollatzResearch.WordTrace tailWord_3709796 prefixEnd_3709796 1904908478127072639788965 := by
  unfold tailWord_3709796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67653688034025074779906621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90204917378700099706542161 67653688034025074779906621)
  ·
    refine ⟨25370133012759403042464983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67653688034025074779906621 25370133012759403042464983)
    ·
      refine ⟨38055199519139104563697475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25370133012759403042464983 38055199519139104563697475)
      ·
        refine ⟨57082799278708656845546213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38055199519139104563697475 57082799278708656845546213)
        ·
          refine ⟨10703024864757873158539915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57082799278708656845546213 10703024864757873158539915)
          ·
            refine ⟨16054537297136809737809873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10703024864757873158539915 16054537297136809737809873)
            ·
              refine ⟨12040902972852607303357405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16054537297136809737809873 12040902972852607303357405)
              ·
                refine ⟨4515338614819727738759027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12040902972852607303357405 4515338614819727738759027)
                ·
                  refine ⟨6773007922229591608138541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515338614819727738759027 6773007922229591608138541)
                  ·
                    refine ⟨2539877970836096853051953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6773007922229591608138541 2539877970836096853051953)
                    ·
                      refine ⟨1904908478127072639788965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2539877970836096853051953 1904908478127072639788965)
                      ·
                        rfl

theorem cell23_3709796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_3709796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709796 prefixEnd_3709796 := by exact prefixLift 3709796
  have htrace : WordTrace (prefixWord ++ tailWord_3709796) baseStart_3709796 baseEnd_3709796 := by
    simpa [prefixWord, tailWord_3709796, baseEnd_3709796] using wordTrace_append hprefix tailTrace_3709796
  have hstable : (prefixWord ++ tailWord_3709796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709796).length < 2 ^ (prefixWord ++ tailWord_3709796).sum := by decide
  have hdescent : baseEnd_3709796 < baseStart_3709796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709876 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3709876 : Nat := 118140960795 + 3709876 * 2 ^ 59
def prefixEnd_3709876 : Nat := 4983230072969 + 3 ^ 40 * 3709876 * 2
def baseEnd_3709876 : Nat := 1904949556579432326788597

theorem tailTrace_3709876 : CollatzResearch.WordTrace tailWord_3709876 prefixEnd_3709876 1904949556579432326788597 := by
  unfold tailWord_3709876
  simp only [CollatzResearch.WordTrace]
  refine ⟨67655146953880161611362741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90206862605173548815150321 67655146953880161611362741)
  ·
    refine ⟨6342670026926265151065257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67655146953880161611362741 6342670026926265151065257)
    ·
      refine ⟨4757002520194698863298943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6342670026926265151065257 4757002520194698863298943)
      ·
        refine ⟨7135503780292048294948415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757002520194698863298943 7135503780292048294948415)
        ·
          refine ⟨10703255670438072442422623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135503780292048294948415 10703255670438072442422623)
          ·
            refine ⟨16054883505657108663633935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10703255670438072442422623 16054883505657108663633935)
            ·
              refine ⟨24082325258485662995450903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16054883505657108663633935 24082325258485662995450903)
              ·
                refine ⟨36123487887728494493176355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24082325258485662995450903 36123487887728494493176355)
                ·
                  refine ⟨54185231831592741739764533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36123487887728494493176355 54185231831592741739764533)
                  ·
                    refine ⟨5079865484211819538102925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54185231831592741739764533 5079865484211819538102925)
                    ·
                      refine ⟨1904949556579432326788597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5079865484211819538102925 1904949556579432326788597)
                      ·
                        rfl

theorem cell23_3709876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3709876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709876 prefixEnd_3709876 := by exact prefixLift 3709876
  have htrace : WordTrace (prefixWord ++ tailWord_3709876) baseStart_3709876 baseEnd_3709876 := by
    simpa [prefixWord, tailWord_3709876, baseEnd_3709876] using wordTrace_append hprefix tailTrace_3709876
  have hstable : (prefixWord ++ tailWord_3709876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709876).length < 2 ^ (prefixWord ++ tailWord_3709876).sum := by decide
  have hdescent : baseEnd_3709876 < baseStart_3709876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709882 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_3709882 : Nat := 118140960795 + 3709882 * 2 ^ 59
def prefixEnd_3709882 : Nat := 4983230072969 + 3 ^ 40 * 3709882 * 2
def baseEnd_3709882 : Nat := 1904952637463359303313569

theorem tailTrace_3709882 : CollatzResearch.WordTrace tailWord_3709882 prefixEnd_3709882 1904952637463359303313569 := by
  unfold tailWord_3709882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33827628186434646561860975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90207008497159057498295933 33827628186434646561860975)
  ·
    refine ⟨50741442279651969842791463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33827628186434646561860975 50741442279651969842791463)
    ·
      refine ⟨76112163419477954764187195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50741442279651969842791463 76112163419477954764187195)
      ·
        refine ⟨114168245129216932146280793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76112163419477954764187195 114168245129216932146280793)
        ·
          refine ⟨85626183846912699109710595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114168245129216932146280793 85626183846912699109710595)
          ·
            refine ⟨128439275770369048664565893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85626183846912699109710595 128439275770369048664565893)
            ·
              refine ⟨24082364206944196624606105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128439275770369048664565893 24082364206944196624606105)
              ·
                refine ⟨18061773155208147468454579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24082364206944196624606105 18061773155208147468454579)
                ·
                  refine ⟨27092659732812221202681869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18061773155208147468454579 27092659732812221202681869)
                  ·
                    refine ⟨10159747399804582951005701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27092659732812221202681869 10159747399804582951005701)
                    ·
                      refine ⟨1904952637463359303313569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10159747399804582951005701 1904952637463359303313569)
                      ·
                        rfl

theorem cell23_3709882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_3709882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709882 prefixEnd_3709882 := by exact prefixLift 3709882
  have htrace : WordTrace (prefixWord ++ tailWord_3709882) baseStart_3709882 baseEnd_3709882 := by
    simpa [prefixWord, tailWord_3709882, baseEnd_3709882] using wordTrace_append hprefix tailTrace_3709882
  have hstable : (prefixWord ++ tailWord_3709882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709882).length < 2 ^ (prefixWord ++ tailWord_3709882).sum := by decide
  have hdescent : baseEnd_3709882 < baseStart_3709882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709896 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 2, 5]
def baseStart_3709896 : Nat := 118140960795 + 3709896 * 2 ^ 59
def prefixEnd_3709896 : Nat := 4983230072969 + 3 ^ 40 * 3709896 * 2
def baseEnd_3709896 : Nat := 634986608730840749512835

theorem tailTrace_3709896 : CollatzResearch.WordTrace tailWord_3709896 prefixEnd_3709896 634986608730840749512835 := by
  unfold tailWord_3709896
  simp only [CollatzResearch.WordTrace]
  refine ⟨67655511683843933319226771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90207348911791911092302361 67655511683843933319226771)
  ·
    refine ⟨101483267525765899978840157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67655511683843933319226771 101483267525765899978840157)
    ·
      refine ⟨38056225322162212492065059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101483267525765899978840157 38056225322162212492065059)
      ·
        refine ⟨57084337983243318738097589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38056225322162212492065059 57084337983243318738097589)
        ·
          refine ⟨5351656685929061131696649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57084337983243318738097589 5351656685929061131696649)
          ·
            refine ⟨4013742514446795848772487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5351656685929061131696649 4013742514446795848772487)
            ·
              refine ⟨6020613771670193773158731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013742514446795848772487 6020613771670193773158731)
              ·
                refine ⟨9030920657505290659738097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020613771670193773158731 9030920657505290659738097)
                ·
                  refine ⟨6773190493128967994803573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9030920657505290659738097 6773190493128967994803573)
                  ·
                    refine ⟨634986608730840749512835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6773190493128967994803573 634986608730840749512835)
                    ·
                      rfl

theorem cell23_3709896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_3709896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709896 prefixEnd_3709896 := by exact prefixLift 3709896
  have htrace : WordTrace (prefixWord ++ tailWord_3709896) baseStart_3709896 baseEnd_3709896 := by
    simpa [prefixWord, tailWord_3709896, baseEnd_3709896] using wordTrace_append hprefix tailTrace_3709896
  have hstable : (prefixWord ++ tailWord_3709896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709896).length < 2 ^ (prefixWord ++ tailWord_3709896).sum := by decide
  have hdescent : baseEnd_3709896 < baseStart_3709896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709899 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 4]
def baseStart_3709899 : Nat := 118140960795 + 3709899 * 2 ^ 59
def prefixEnd_3709899 : Nat := 4983230072969 + 3 ^ 40 * 3709899 * 2
def baseEnd_3709899 : Nat := 1904961366634485736800991

theorem tailTrace_3709899 : CollatzResearch.WordTrace tailWord_3709899 prefixEnd_3709899 1904961366634485736800991 := by
  unfold tailWord_3709899
  simp only [CollatzResearch.WordTrace]
  refine ⟨135311132786676998150812751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90207421857784665433875167 135311132786676998150812751)
  ·
    refine ⟨202966699180015497226219127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135311132786676998150812751 202966699180015497226219127)
    ·
      refine ⟨304450048770023245839328691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202966699180015497226219127 304450048770023245839328691)
      ·
        refine ⟨456675073155034868758993037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304450048770023245839328691 456675073155034868758993037)
        ·
          refine ⟨171253152433138075784622389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456675073155034868758993037 171253152433138075784622389)
          ·
            refine ⟨16054983040606694604808349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171253152433138075784622389 16054983040606694604808349)
            ·
              refine ⟨6020618640227510476803131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16054983040606694604808349 6020618640227510476803131)
              ·
                refine ⟨9030927960341265715204697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020618640227510476803131 9030927960341265715204697)
                ·
                  refine ⟨6773195970255949286403523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9030927960341265715204697 6773195970255949286403523)
                  ·
                    refine ⟨10159793955383923929605285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6773195970255949286403523 10159793955383923929605285)
                    ·
                      refine ⟨1904961366634485736800991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10159793955383923929605285 1904961366634485736800991)
                      ·
                        rfl

theorem cell23_3709899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 4].length) (baseStart_3709899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709899 prefixEnd_3709899 := by exact prefixLift 3709899
  have htrace : WordTrace (prefixWord ++ tailWord_3709899) baseStart_3709899 baseEnd_3709899 := by
    simpa [prefixWord, tailWord_3709899, baseEnd_3709899] using wordTrace_append hprefix tailTrace_3709899
  have hstable : (prefixWord ++ tailWord_3709899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709899).length < 2 ^ (prefixWord ++ tailWord_3709899).sum := by decide
  have hdescent : baseEnd_3709899 < baseStart_3709899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709912 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3709912 : Nat := 118140960795 + 3709912 * 2 ^ 59
def prefixEnd_3709912 : Nat := 4983230072969 + 3 ^ 40 * 3709912 * 2
def baseEnd_3709912 : Nat := 1904968041882994185938431

theorem tailTrace_3709912 : CollatzResearch.WordTrace tailWord_3709912 prefixEnd_3709912 1904968041882994185938431 := by
  unfold tailWord_3709912
  simp only [CollatzResearch.WordTrace]
  refine ⟨67655803467814950685517995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90207737957086600914023993 67655803467814950685517995)
  ·
    refine ⟨101483705201722426028276993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67655803467814950685517995 101483705201722426028276993)
    ·
      refine ⟨76112778901291819521207745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101483705201722426028276993 76112778901291819521207745)
      ·
        refine ⟨57084584175968864640905809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76112778901291819521207745 57084584175968864640905809)
        ·
          refine ⟨42813438131976648480679357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57084584175968864640905809 42813438131976648480679357)
          ·
            refine ⟨16055039299491243180254759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42813438131976648480679357 16055039299491243180254759)
            ·
              refine ⟨24082558949236864770382139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16055039299491243180254759 24082558949236864770382139)
              ·
                refine ⟨36123838423855297155573209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24082558949236864770382139 36123838423855297155573209)
                ·
                  refine ⟨27092878817891472866679907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36123838423855297155573209 27092878817891472866679907)
                  ·
                    refine ⟨40639318226837209300019861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27092878817891472866679907 40639318226837209300019861)
                    ·
                      refine ⟨1904968041882994185938431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40639318226837209300019861 1904968041882994185938431)
                      ·
                        rfl

theorem cell23_3709912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3709912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709912 prefixEnd_3709912 := by exact prefixLift 3709912
  have htrace : WordTrace (prefixWord ++ tailWord_3709912) baseStart_3709912 baseEnd_3709912 := by
    simpa [prefixWord, tailWord_3709912, baseEnd_3709912] using wordTrace_append hprefix tailTrace_3709912
  have hstable : (prefixWord ++ tailWord_3709912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709912).length < 2 ^ (prefixWord ++ tailWord_3709912).sum := by decide
  have hdescent : baseEnd_3709912 < baseStart_3709912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709952 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 7, 5]
def baseStart_3709952 : Nat := 118140960795 + 3709952 * 2 ^ 59
def prefixEnd_3709952 : Nat := 4983230072969 + 3 ^ 40 * 3709952 * 2
def baseEnd_3709952 : Nat := 634996193703058009812749

theorem tailTrace_3709952 : CollatzResearch.WordTrace tailWord_3709952 prefixEnd_3709952 634996193703058009812749 := by
  unfold tailWord_3709952
  simp only [CollatzResearch.WordTrace]
  refine ⟨67656532927742494101246055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90208710570323325468328073 67656532927742494101246055)
  ·
    refine ⟨101484799391613741151869083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67656532927742494101246055 101484799391613741151869083)
    ·
      refine ⟨152227199087420611727803625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101484799391613741151869083 152227199087420611727803625)
      ·
        refine ⟨114170399315565458795852719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152227199087420611727803625 114170399315565458795852719)
        ·
          refine ⟨171255598973348188193779079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114170399315565458795852719 171255598973348188193779079)
          ·
            refine ⟨256883398460022282290668619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171255598973348188193779079 256883398460022282290668619)
            ·
              refine ⟨385325097690033423436002929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256883398460022282290668619 385325097690033423436002929)
              ·
                refine ⟨288993823267525067577002197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385325097690033423436002929 288993823267525067577002197)
                ·
                  refine ⟨6773292732832618771335989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 288993823267525067577002197 6773292732832618771335989)
                  ·
                    refine ⟨634996193703058009812749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6773292732832618771335989 634996193703058009812749)
                    ·
                      rfl

theorem cell23_3709952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_3709952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709952 prefixEnd_3709952 := by exact prefixLift 3709952
  have htrace : WordTrace (prefixWord ++ tailWord_3709952) baseStart_3709952 baseEnd_3709952 := by
    simpa [prefixWord, tailWord_3709952, baseEnd_3709952] using wordTrace_append hprefix tailTrace_3709952
  have hstable : (prefixWord ++ tailWord_3709952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709952).length < 2 ^ (prefixWord ++ tailWord_3709952).sum := by decide
  have hdescent : baseEnd_3709952 < baseStart_3709952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709976 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 4, 3, 2]
def baseStart_3709976 : Nat := 118140960795 + 3709976 * 2 ^ 59
def prefixEnd_3709976 : Nat := 4983230072969 + 3 ^ 40 * 3709976 * 2
def baseEnd_3709976 : Nat := 1905000904644881935538137

theorem tailTrace_3709976 : CollatzResearch.WordTrace tailWord_3709976 prefixEnd_3709976 1905000904644881935538137 := by
  unfold tailWord_3709976
  simp only [CollatzResearch.WordTrace]
  refine ⟨67656970603699020150682891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90209294138265360200910521 67656970603699020150682891)
  ·
    refine ⟨101485455905548530226024337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67656970603699020150682891 101485455905548530226024337)
    ·
      refine ⟨76114091929161397669518253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101485455905548530226024337 76114091929161397669518253)
      ·
        refine ⟨28542784473435524126069345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76114091929161397669518253 28542784473435524126069345)
        ·
          refine ⟨21407088355076643094552009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28542784473435524126069345 21407088355076643094552009)
          ·
            refine ⟨16055316266307482320914007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21407088355076643094552009 16055316266307482320914007)
            ·
              refine ⟨24082974399461223481371011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16055316266307482320914007 24082974399461223481371011)
              ·
                refine ⟨36124461599191835222056517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24082974399461223481371011 36124461599191835222056517)
                ·
                  refine ⟨6773336549848469104135597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36124461599191835222056517 6773336549848469104135597)
                  ·
                    refine ⟨2540001206193175914050849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6773336549848469104135597 2540001206193175914050849)
                    ·
                      refine ⟨1905000904644881935538137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540001206193175914050849 1905000904644881935538137)
                      ·
                        rfl

theorem cell23_3709976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_3709976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709976 prefixEnd_3709976 := by exact prefixLift 3709976
  have htrace : WordTrace (prefixWord ++ tailWord_3709976) baseStart_3709976 baseEnd_3709976 := by
    simpa [prefixWord, tailWord_3709976, baseEnd_3709976] using wordTrace_append hprefix tailTrace_3709976
  have hstable : (prefixWord ++ tailWord_3709976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709976).length < 2 ^ (prefixWord ++ tailWord_3709976).sum := by decide
  have hdescent : baseEnd_3709976 < baseStart_3709976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709983 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 3]
def baseStart_3709983 : Nat := 118140960795 + 3709983 * 2 ^ 59
def prefixEnd_3709983 : Nat := 4983230072969 + 3 ^ 40 * 3709983 * 2
def baseEnd_3709983 : Nat := 1905004499009463408150605

theorem tailTrace_3709983 : CollatzResearch.WordTrace tailWord_3709983 prefixEnd_3709983 1905004499009463408150605 := by
  unfold tailWord_3709983
  simp only [CollatzResearch.WordTrace]
  refine ⟨135314196518372680496870603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90209464345581786997913735 135314196518372680496870603)
  ·
    refine ⟨202971294777559020745305905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135314196518372680496870603 202971294777559020745305905)
    ·
      refine ⟨152228471083169265558979429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202971294777559020745305905 152228471083169265558979429)
      ·
        refine ⟨28542838328094237292308643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152228471083169265558979429 28542838328094237292308643)
        ·
          refine ⟨42814257492141355938462965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28542838328094237292308643 42814257492141355938462965)
          ·
            refine ⟨4013836639888252119230903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42814257492141355938462965 4013836639888252119230903)
            ·
              refine ⟨6020754959832378178846355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013836639888252119230903 6020754959832378178846355)
              ·
                refine ⟨9031132439748567268269533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020754959832378178846355 9031132439748567268269533)
                ·
                  refine ⟨3386674664905712725601075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9031132439748567268269533 3386674664905712725601075)
                  ·
                    refine ⟨5080011997358569088401613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3386674664905712725601075 5080011997358569088401613)
                    ·
                      refine ⟨1905004499009463408150605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080011997358569088401613 1905004499009463408150605)
                      ·
                        rfl

theorem cell23_3709983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_3709983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709983 prefixEnd_3709983 := by exact prefixLift 3709983
  have htrace : WordTrace (prefixWord ++ tailWord_3709983) baseStart_3709983 baseEnd_3709983 := by
    simpa [prefixWord, tailWord_3709983, baseEnd_3709983] using wordTrace_append hprefix tailTrace_3709983
  have hstable : (prefixWord ++ tailWord_3709983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709983).length < 2 ^ (prefixWord ++ tailWord_3709983).sum := by decide
  have hdescent : baseEnd_3709983 < baseStart_3709983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709989 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3709989 : Nat := 118140960795 + 3709989 * 2 ^ 59
def prefixEnd_3709989 : Nat := 4983230072969 + 3 ^ 40 * 3709989 * 2
def baseEnd_3709989 : Nat := 1905007579893390384675577

theorem tailTrace_3709989 : CollatzResearch.WordTrace tailWord_3709989 prefixEnd_3709989 1905007579893390384675577 := by
  unfold tailWord_3709989
  simp only [CollatzResearch.WordTrace]
  refine ⟨135314415356350943521589021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90209610237567295681059347 135314415356350943521589021)
  ·
    refine ⟨50742905758631603820595883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135314415356350943521589021 50742905758631603820595883)
    ·
      refine ⟨76114358637947405730893825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50742905758631603820595883 76114358637947405730893825)
      ·
        refine ⟨57085768978460554298170369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76114358637947405730893825 57085768978460554298170369)
        ·
          refine ⟨42814326733845415723627777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57085768978460554298170369 42814326733845415723627777)
          ·
            refine ⟨32110745050384061792720833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42814326733845415723627777 32110745050384061792720833)
            ·
              refine ⟨24083058787788046344540625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32110745050384061792720833 24083058787788046344540625)
              ·
                refine ⟨18062294090841034758405469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24083058787788046344540625 18062294090841034758405469)
                ·
                  refine ⟨6773360284065388034402051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18062294090841034758405469 6773360284065388034402051)
                  ·
                    refine ⟨10160040426098082051603077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6773360284065388034402051 10160040426098082051603077)
                    ·
                      refine ⟨1905007579893390384675577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10160040426098082051603077 1905007579893390384675577)
                      ·
                        rfl

theorem cell23_3709989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3709989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3709989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3709989 prefixEnd_3709989 := by exact prefixLift 3709989
  have htrace : WordTrace (prefixWord ++ tailWord_3709989) baseStart_3709989 baseEnd_3709989 := by
    simpa [prefixWord, tailWord_3709989, baseEnd_3709989] using wordTrace_append hprefix tailTrace_3709989
  have hstable : (prefixWord ++ tailWord_3709989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709989).length < 2 ^ (prefixWord ++ tailWord_3709989).sum := by decide
  have hdescent : baseEnd_3709989 < baseStart_3709989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710019 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4]
def baseStart_3710019 : Nat := 118140960795 + 3710019 * 2 ^ 59
def prefixEnd_3710019 : Nat := 4983230072969 + 3 ^ 40 * 3710019 * 2
def baseEnd_3710019 : Nat := 1905022984313025267300439

theorem tailTrace_3710019 : CollatzResearch.WordTrace tailWord_3710019 prefixEnd_3710019 1905022984313025267300439 := by
  unfold tailWord_3710019
  simp only [CollatzResearch.WordTrace]
  refine ⟨135315509546242258645181111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90210339697494839096787407 135315509546242258645181111)
  ·
    refine ⟨202973264319363387967771667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135315509546242258645181111 202973264319363387967771667)
    ·
      refine ⟨304459896479045081951657501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202973264319363387967771667 304459896479045081951657501)
      ·
        refine ⟨114172461179641905731871563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304459896479045081951657501 114172461179641905731871563)
        ·
          refine ⟨171258691769462858597807345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114172461179641905731871563 171258691769462858597807345)
          ·
            refine ⟨128444018827097143948355509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171258691769462858597807345 128444018827097143948355509)
            ·
              refine ⟨12041626765040357245158329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128444018827097143948355509 12041626765040357245158329)
              ·
                refine ⟨9031220073780267933868747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12041626765040357245158329 9031220073780267933868747)
                ·
                  refine ⟨13546830110670401900803121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9031220073780267933868747 13546830110670401900803121)
                  ·
                    refine ⟨10160122583002801425602341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13546830110670401900803121 10160122583002801425602341)
                    ·
                      refine ⟨1905022984313025267300439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10160122583002801425602341 1905022984313025267300439)
                      ·
                        rfl

theorem cell23_3710019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_3710019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710019 prefixEnd_3710019 := by exact prefixLift 3710019
  have htrace : WordTrace (prefixWord ++ tailWord_3710019) baseStart_3710019 baseEnd_3710019 := by
    simpa [prefixWord, tailWord_3710019, baseEnd_3710019] using wordTrace_append hprefix tailTrace_3710019
  have hstable : (prefixWord ++ tailWord_3710019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710019).length < 2 ^ (prefixWord ++ tailWord_3710019).sum := by decide
  have hdescent : baseEnd_3710019 < baseStart_3710019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710023 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_3710023 : Nat := 118140960795 + 3710023 * 2 ^ 59
def prefixEnd_3710023 : Nat := 4983230072969 + 3 ^ 40 * 3710023 * 2
def baseEnd_3710023 : Nat := 1905025038235643251650421

theorem tailTrace_3710023 : CollatzResearch.WordTrace tailWord_3710023 prefixEnd_3710023 1905025038235643251650421 := by
  unfold tailWord_3710023
  simp only [CollatzResearch.WordTrace]
  refine ⟨135315655438227767328326723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90210436958818511552217815 135315655438227767328326723)
  ·
    refine ⟨202973483157341650992490085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135315655438227767328326723 202973483157341650992490085)
    ·
      refine ⟨38057528092001559561091891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202973483157341650992490085 38057528092001559561091891)
      ·
        refine ⟨57086292138002339341637837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38057528092001559561091891 57086292138002339341637837)
        ·
          refine ⟨21407359551750877253114189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57086292138002339341637837 21407359551750877253114189)
          ·
            refine ⟨8027759831906578969917821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21407359551750877253114189 8027759831906578969917821)
            ·
              refine ⟨3010409936964967113719183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8027759831906578969917821 3010409936964967113719183)
              ·
                refine ⟨4515614905447450670578775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010409936964967113719183 4515614905447450670578775)
                ·
                  refine ⟨6773422358171176005868163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515614905447450670578775 6773422358171176005868163)
                  ·
                    refine ⟨10160133537256764008802245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6773422358171176005868163 10160133537256764008802245)
                    ·
                      refine ⟨1905025038235643251650421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10160133537256764008802245 1905025038235643251650421)
                      ·
                        rfl

theorem cell23_3710023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_3710023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710023 prefixEnd_3710023 := by exact prefixLift 3710023
  have htrace : WordTrace (prefixWord ++ tailWord_3710023) baseStart_3710023 baseEnd_3710023 := by
    simpa [prefixWord, tailWord_3710023, baseEnd_3710023] using wordTrace_append hprefix tailTrace_3710023
  have hstable : (prefixWord ++ tailWord_3710023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710023).length < 2 ^ (prefixWord ++ tailWord_3710023).sum := by decide
  have hdescent : baseEnd_3710023 < baseStart_3710023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710026 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_3710026 : Nat := 118140960795 + 3710026 * 2 ^ 59
def prefixEnd_3710026 : Nat := 4983230072969 + 3 ^ 40 * 3710026 * 2
def baseEnd_3710026 : Nat := 1905026578677606739912907

theorem tailTrace_3710026 : CollatzResearch.WordTrace tailWord_3710026 prefixEnd_3710026 1905026578677606739912907 := by
  unfold tailWord_3710026
  simp only [CollatzResearch.WordTrace]
  refine ⟨33828941214304224710171483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90210509904811265893790621 33828941214304224710171483)
  ·
    refine ⟨50743411821456337065257225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33828941214304224710171483 50743411821456337065257225)
    ·
      refine ⟨38057558866092252798942919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50743411821456337065257225 38057558866092252798942919)
      ·
        refine ⟨57086338299138379198414379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38057558866092252798942919 57086338299138379198414379)
        ·
          refine ⟨85629507448707568797621569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57086338299138379198414379 85629507448707568797621569)
          ·
            refine ⟨64222130586530676598216177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85629507448707568797621569 64222130586530676598216177)
            ·
              refine ⟨48166597939898007448662133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64222130586530676598216177 48166597939898007448662133)
              ·
                refine ⟨4515618556865438198312075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48166597939898007448662133 4515618556865438198312075)
                ·
                  refine ⟨6773427835298157297468113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515618556865438198312075 6773427835298157297468113)
                  ·
                    refine ⟨5080070876473617973101085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6773427835298157297468113 5080070876473617973101085)
                    ·
                      refine ⟨1905026578677606739912907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080070876473617973101085 1905026578677606739912907)
                      ·
                        rfl

theorem cell23_3710026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_3710026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710026 prefixEnd_3710026 := by exact prefixLift 3710026
  have htrace : WordTrace (prefixWord ++ tailWord_3710026) baseStart_3710026 baseEnd_3710026 := by
    simpa [prefixWord, tailWord_3710026, baseEnd_3710026] using wordTrace_append hprefix tailTrace_3710026
  have hstable : (prefixWord ++ tailWord_3710026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710026).length < 2 ^ (prefixWord ++ tailWord_3710026).sum := by decide
  have hdescent : baseEnd_3710026 < baseStart_3710026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710029 : List Nat := [1, 6, 1, 1, 1, 13]
def baseStart_3710029 : Nat := 118140960795 + 3710029 * 2 ^ 59
def prefixEnd_3710029 : Nat := 4983230072969 + 3 ^ 40 * 3710029 * 2
def baseEnd_3710029 : Nat := 7839621889380947441051

theorem tailTrace_3710029 : CollatzResearch.WordTrace tailWord_3710029 prefixEnd_3710029 7839621889380947441051 := by
  unfold tailWord_3710029
  simp only [CollatzResearch.WordTrace]
  refine ⟨135315874276206030353045141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90210582850804020235363427 135315874276206030353045141)
  ·
    refine ⟨6342931606697157672798991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135315874276206030353045141 6342931606697157672798991)
    ·
      refine ⟨9514397410045736509198487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342931606697157672798991 9514397410045736509198487)
      ·
        refine ⟨14271596115068604763797731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9514397410045736509198487 14271596115068604763797731)
        ·
          refine ⟨21407394172602907145696597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14271596115068604763797731 21407394172602907145696597)
          ·
            refine ⟨7839621889380947441051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 21407394172602907145696597 7839621889380947441051)
            ·
              rfl

theorem cell23_3710029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 13].length) (baseStart_3710029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710029 prefixEnd_3710029 := by exact prefixLift 3710029
  have htrace : WordTrace (prefixWord ++ tailWord_3710029) baseStart_3710029 baseEnd_3710029 := by
    simpa [prefixWord, tailWord_3710029, baseEnd_3710029] using wordTrace_append hprefix tailTrace_3710029
  have hstable : (prefixWord ++ tailWord_3710029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710029).length < 2 ^ (prefixWord ++ tailWord_3710029).sum := by decide
  have hdescent : baseEnd_3710029 < baseStart_3710029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710039 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_3710039 : Nat := 118140960795 + 3710039 * 2 ^ 59
def prefixEnd_3710039 : Nat := 4983230072969 + 3 ^ 40 * 3710039 * 2
def baseEnd_3710039 : Nat := 1905033253926115189050347

theorem tailTrace_3710039 : CollatzResearch.WordTrace tailWord_3710039 prefixEnd_3710039 1905033253926115189050347 := by
  unfold tailWord_3710039
  simp only [CollatzResearch.WordTrace]
  refine ⟨135316239006169802060909171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90210826004113201373939447 135316239006169802060909171)
  ·
    refine ⟨202974358509254703091363757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135316239006169802060909171 202974358509254703091363757)
    ·
      refine ⟨76115384440970513659261409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202974358509254703091363757 76115384440970513659261409)
      ·
        refine ⟨57086538330727885244446057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76115384440970513659261409 57086538330727885244446057)
        ·
          refine ⟨42814903748045913933334543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57086538330727885244446057 42814903748045913933334543)
          ·
            refine ⟨64222355622068870900001815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42814903748045913933334543 64222355622068870900001815)
            ·
              refine ⟨96333533433103306350002723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64222355622068870900001815 96333533433103306350002723)
              ·
                refine ⟨144500300149654959525004085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96333533433103306350002723 144500300149654959525004085)
                ·
                  refine ⟨13546903139030152455469133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144500300149654959525004085 13546903139030152455469133)
                  ·
                    refine ⟨5080088677136307170800925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13546903139030152455469133 5080088677136307170800925)
                    ·
                      refine ⟨1905033253926115189050347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080088677136307170800925 1905033253926115189050347)
                      ·
                        rfl

theorem cell23_3710039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_3710039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710039 prefixEnd_3710039 := by exact prefixLift 3710039
  have htrace : WordTrace (prefixWord ++ tailWord_3710039) baseStart_3710039 baseEnd_3710039 := by
    simpa [prefixWord, tailWord_3710039, baseEnd_3710039] using wordTrace_append hprefix tailTrace_3710039
  have hstable : (prefixWord ++ tailWord_3710039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710039).length < 2 ^ (prefixWord ++ tailWord_3710039).sum := by decide
  have hdescent : baseEnd_3710039 < baseStart_3710039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710040 : List Nat := [2, 1, 2, 2, 1, 3, 3, 4, 1, 2, 2]
def baseStart_3710040 : Nat := 118140960795 + 3710040 * 2 ^ 59
def prefixEnd_3710040 : Nat := 4983230072969 + 3 ^ 40 * 3710040 * 2
def baseEnd_3710040 : Nat := 1905033767406769685137843

theorem tailTrace_3710040 : CollatzResearch.WordTrace tailWord_3710040 prefixEnd_3710040 1905033767406769685137843 := by
  unfold tailWord_3710040
  simp only [CollatzResearch.WordTrace]
  refine ⟨67658137739583089615847787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90210850319444119487797049 67658137739583089615847787)
  ·
    refine ⟨101487206609374634423771681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67658137739583089615847787 101487206609374634423771681)
    ·
      refine ⟨76115404957030975817828761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101487206609374634423771681 76115404957030975817828761)
      ·
        refine ⟨57086553717773231863371571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76115404957030975817828761 57086553717773231863371571)
        ·
          refine ⟨85629830576659847795057357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57086553717773231863371571 85629830576659847795057357)
          ·
            refine ⟨32111186466247442923146509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85629830576659847795057357 32111186466247442923146509)
            ·
              refine ⟨12041694924842791096179941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32111186466247442923146509 12041694924842791096179941)
              ·
                refine ⟨2257817798408023330533739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12041694924842791096179941 2257817798408023330533739)
                ·
                  refine ⟨3386726697612034995800609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2257817798408023330533739 3386726697612034995800609)
                  ·
                    refine ⟨2540045023209026246850457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3386726697612034995800609 2540045023209026246850457)
                    ·
                      refine ⟨1905033767406769685137843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540045023209026246850457 1905033767406769685137843)
                      ·
                        rfl

theorem cell23_3710040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_3710040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710040 prefixEnd_3710040 := by exact prefixLift 3710040
  have htrace : WordTrace (prefixWord ++ tailWord_3710040) baseStart_3710040 baseEnd_3710040 := by
    simpa [prefixWord, tailWord_3710040, baseEnd_3710040] using wordTrace_append hprefix tailTrace_3710040
  have hstable : (prefixWord ++ tailWord_3710040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710040).length < 2 ^ (prefixWord ++ tailWord_3710040).sum := by decide
  have hdescent : baseEnd_3710040 < baseStart_3710040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710083 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 1, 3, 2]
def baseStart_3710083 : Nat := 118140960795 + 3710083 * 2 ^ 59
def prefixEnd_3710083 : Nat := 4983230072969 + 3 ^ 40 * 3710083 * 2
def baseEnd_3710083 : Nat := 1905055847074913016900145

theorem tailTrace_3710083 : CollatzResearch.WordTrace tailWord_3710083 prefixEnd_3710083 1905055847074913016900145 := by
  unfold tailWord_3710083
  simp only [CollatzResearch.WordTrace]
  refine ⟨135317843818010397575510903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90211895878673598383673935 135317843818010397575510903)
  ·
    refine ⟨202976765727015596363266355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135317843818010397575510903 202976765727015596363266355)
    ·
      refine ⟨304465148590523394544899533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202976765727015596363266355 304465148590523394544899533)
      ·
        refine ⟨114174430721446272954337325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304465148590523394544899533 114174430721446272954337325)
        ·
          refine ⟨42815411520542352357876497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114174430721446272954337325 42815411520542352357876497)
          ·
            refine ⟨32111558640406764268407373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42815411520542352357876497 32111558640406764268407373)
            ·
              refine ⟨12041834490152536600652765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32111558640406764268407373 12041834490152536600652765)
              ·
                refine ⟨4515687933807201225244787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12041834490152536600652765 4515687933807201225244787)
                ·
                  refine ⟨6773531900710801837867181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515687933807201225244787 6773531900710801837867181)
                  ·
                    refine ⟨2540074462766550689200193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6773531900710801837867181 2540074462766550689200193)
                    ·
                      refine ⟨1905055847074913016900145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540074462766550689200193 1905055847074913016900145)
                      ·
                        rfl

theorem cell23_3710083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_3710083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710083 prefixEnd_3710083 := by exact prefixLift 3710083
  have htrace : WordTrace (prefixWord ++ tailWord_3710083) baseStart_3710083 baseEnd_3710083 := by
    simpa [prefixWord, tailWord_3710083, baseEnd_3710083] using wordTrace_append hprefix tailTrace_3710083
  have hstable : (prefixWord ++ tailWord_3710083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710083).length < 2 ^ (prefixWord ++ tailWord_3710083).sum := by decide
  have hdescent : baseEnd_3710083 < baseStart_3710083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710089 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 2, 6]
def baseStart_3710089 : Nat := 118140960795 + 3710089 * 2 ^ 59
def prefixEnd_3710089 : Nat := 4983230072969 + 3 ^ 40 * 3710089 * 2
def baseEnd_3710089 : Nat := 635019642652946664475039

theorem tailTrace_3710089 : CollatzResearch.WordTrace tailWord_3710089 prefixEnd_3710089 635019642652946664475039 := by
  unfold tailWord_3710089
  simp only [CollatzResearch.WordTrace]
  refine ⟨135318062655988660600229321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90212041770659107066819547 135318062655988660600229321)
  ·
    refine ⟨101488546991991495450171991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135318062655988660600229321 101488546991991495450171991)
    ·
      refine ⟨152232820487987243175257987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101488546991991495450171991 152232820487987243175257987)
      ·
        refine ⟨228349230731980864762886981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152232820487987243175257987 228349230731980864762886981)
        ·
          refine ⟨42815480762246412143041309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228349230731980864762886981 42815480762246412143041309)
          ·
            refine ⟨16055805285842404553640491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42815480762246412143041309 16055805285842404553640491)
            ·
              refine ⟨24083707928763606830460737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16055805285842404553640491 24083707928763606830460737)
              ·
                refine ⟨18062780946572705122845553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24083707928763606830460737 18062780946572705122845553)
                ·
                  refine ⟨13547085709929528842134165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18062780946572705122845553 13547085709929528842134165)
                  ·
                    refine ⟨635019642652946664475039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13547085709929528842134165 635019642652946664475039)
                    ·
                      rfl

theorem cell23_3710089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_3710089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710089 prefixEnd_3710089 := by exact prefixLift 3710089
  have htrace : WordTrace (prefixWord ++ tailWord_3710089) baseStart_3710089 baseEnd_3710089 := by
    simpa [prefixWord, tailWord_3710089, baseEnd_3710089] using wordTrace_append hprefix tailTrace_3710089
  have hstable : (prefixWord ++ tailWord_3710089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710089).length < 2 ^ (prefixWord ++ tailWord_3710089).sum := by decide
  have hdescent : baseEnd_3710089 < baseStart_3710089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710099 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 3]
def baseStart_3710099 : Nat := 118140960795 + 3710099 * 2 ^ 59
def prefixEnd_3710099 : Nat := 4983230072969 + 3 ^ 40 * 3710099 * 2
def baseEnd_3710099 : Nat := 1905064062765384954300071

theorem tailTrace_3710099 : CollatzResearch.WordTrace tailWord_3710099 prefixEnd_3710099 1905064062765384954300071 := by
  unfold tailWord_3710099
  simp only [CollatzResearch.WordTrace]
  refine ⟨135318427385952432308093351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90212284923968288205395567 135318427385952432308093351)
  ·
    refine ⟨202977641078928648462140027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135318427385952432308093351 202977641078928648462140027)
    ·
      refine ⟨304466461618392972693210041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202977641078928648462140027 304466461618392972693210041)
      ·
        refine ⟨228349846213794729519907531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304466461618392972693210041 228349846213794729519907531)
        ·
          refine ⟨342524769320692094279861297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228349846213794729519907531 342524769320692094279861297)
          ·
            refine ⟨256893576990519070709895973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342524769320692094279861297 256893576990519070709895973)
            ·
              refine ⟨48167545685722325758105495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256893576990519070709895973 48167545685722325758105495)
              ·
                refine ⟨72251318528583488637158243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48167545685722325758105495 72251318528583488637158243)
                ·
                  refine ⟨108376977792875232955737365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72251318528583488637158243 108376977792875232955737365)
                  ·
                    refine ⟨5080170834041026544800189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108376977792875232955737365 5080170834041026544800189)
                    ·
                      refine ⟨1905064062765384954300071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080170834041026544800189 1905064062765384954300071)
                      ·
                        rfl

theorem cell23_3710099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_3710099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710099 prefixEnd_3710099 := by exact prefixLift 3710099
  have htrace : WordTrace (prefixWord ++ tailWord_3710099) baseStart_3710099 baseEnd_3710099 := by
    simpa [prefixWord, tailWord_3710099, baseEnd_3710099] using wordTrace_append hprefix tailTrace_3710099
  have hstable : (prefixWord ++ tailWord_3710099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710099).length < 2 ^ (prefixWord ++ tailWord_3710099).sum := by decide
  have hdescent : baseEnd_3710099 < baseStart_3710099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710106 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_3710106 : Nat := 118140960795 + 3710106 * 2 ^ 59
def prefixEnd_3710106 : Nat := 4983230072969 + 3 ^ 40 * 3710106 * 2
def baseEnd_3710106 : Nat := 635022552376655475637513

theorem tailTrace_3710106 : CollatzResearch.WordTrace tailWord_3710106 prefixEnd_3710106 635022552376655475637513 := by
  unfold tailWord_3710106
  simp only [CollatzResearch.WordTrace]
  refine ⟨33829670674231768125899543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90212455131284715002398781 33829670674231768125899543)
  ·
    refine ⟨50744506011347652188849315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33829670674231768125899543 50744506011347652188849315)
    ·
      refine ⟨76116759017021478283273973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50744506011347652188849315 76116759017021478283273973)
      ·
        refine ⟨7135946157845763589056935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76116759017021478283273973 7135946157845763589056935)
        ·
          refine ⟨10703919236768645383585403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135946157845763589056935 10703919236768645383585403)
          ·
            refine ⟨16055878855152968075378105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10703919236768645383585403 16055878855152968075378105)
            ·
              refine ⟨12041909141364726056533579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16055878855152968075378105 12041909141364726056533579)
              ·
                refine ⟨18062863712047089084800369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12041909141364726056533579 18062863712047089084800369)
                ·
                  refine ⟨13547147784035316813600277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18062863712047089084800369 13547147784035316813600277)
                  ·
                    refine ⟨635022552376655475637513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13547147784035316813600277 635022552376655475637513)
                    ·
                      rfl

theorem cell23_3710106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_3710106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710106 prefixEnd_3710106 := by exact prefixLift 3710106
  have htrace : WordTrace (prefixWord ++ tailWord_3710106) baseStart_3710106 baseEnd_3710106 := by
    simpa [prefixWord, tailWord_3710106, baseEnd_3710106] using wordTrace_append hprefix tailTrace_3710106
  have hstable : (prefixWord ++ tailWord_3710106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710106).length < 2 ^ (prefixWord ++ tailWord_3710106).sum := by decide
  have hdescent : baseEnd_3710106 < baseStart_3710106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710136 : List Nat := [2, 1, 2, 1, 2, 1, 2, 7, 5]
def baseStart_3710136 : Nat := 118140960795 + 3710136 * 2 ^ 59
def prefixEnd_3710136 : Nat := 4983230072969 + 3 ^ 40 * 3710136 * 2
def baseEnd_3710136 : Nat := 211675895727733478837489

theorem tailTrace_3710136 : CollatzResearch.WordTrace tailWord_3710136 prefixEnd_3710136 211675895727733478837489 := by
  unfold tailWord_3710136
  simp only [CollatzResearch.WordTrace]
  refine ⟨67659888443409193813595131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90213184591212258418126841 67659888443409193813595131)
  ·
    refine ⟨101489832665113790720392697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67659888443409193813595131 101489832665113790720392697)
    ·
      refine ⟨76117374498835343040294523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101489832665113790720392697 76117374498835343040294523)
      ·
        refine ⟨114176061748253014560441785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76117374498835343040294523 114176061748253014560441785)
        ·
          refine ⟨85632046311189760920331339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114176061748253014560441785 85632046311189760920331339)
          ·
            refine ⟨128448069466784641380497009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85632046311189760920331339 128448069466784641380497009)
            ·
              refine ⟨96336052100088481035372757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128448069466784641380497009 96336052100088481035372757)
              ·
                refine ⟨2257876221095823774266549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96336052100088481035372757 2257876221095823774266549)
                ·
                  refine ⟨211675895727733478837489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2257876221095823774266549 211675895727733478837489)
                  ·
                    rfl

theorem cell23_3710136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 5].length) (baseStart_3710136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710136 prefixEnd_3710136 := by exact prefixLift 3710136
  have htrace : WordTrace (prefixWord ++ tailWord_3710136) baseStart_3710136 baseEnd_3710136 := by
    simpa [prefixWord, tailWord_3710136, baseEnd_3710136] using wordTrace_append hprefix tailTrace_3710136
  have hstable : (prefixWord ++ tailWord_3710136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710136).length < 2 ^ (prefixWord ++ tailWord_3710136).sum := by decide
  have hdescent : baseEnd_3710136 < baseStart_3710136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710164 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3710164 : Nat := 118140960795 + 3710164 * 2 ^ 59
def prefixEnd_3710164 : Nat := 4983230072969 + 3 ^ 40 * 3710164 * 2
def baseEnd_3710164 : Nat := 1905097439007927199987273

theorem tailTrace_3710164 : CollatzResearch.WordTrace tailWord_3710164 prefixEnd_3710164 1905097439007927199987273 := by
  unfold tailWord_3710164
  simp only [CollatzResearch.WordTrace]
  refine ⟨67660399065358474204604773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90213865420477965606139697 67660399065358474204604773)
  ·
    refine ⟨12686324824754713913363395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67660399065358474204604773 12686324824754713913363395)
    ·
      refine ⟨19029487237132070870045093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12686324824754713913363395 19029487237132070870045093)
      ·
        refine ⟨3568028856962263288133455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19029487237132070870045093 3568028856962263288133455)
        ·
          refine ⟨5352043285443394932200183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3568028856962263288133455 5352043285443394932200183)
          ·
            refine ⟨8028064928165092398300275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352043285443394932200183 8028064928165092398300275)
            ·
              refine ⟨12042097392247638597450413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8028064928165092398300275 12042097392247638597450413)
              ·
                refine ⟨4515786522092864474043905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12042097392247638597450413 4515786522092864474043905)
                ·
                  refine ⟨3386839891569648355532929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515786522092864474043905 3386839891569648355532929)
                  ·
                    refine ⟨2540129918677236266649697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3386839891569648355532929 2540129918677236266649697)
                    ·
                      refine ⟨1905097439007927199987273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540129918677236266649697 1905097439007927199987273)
                      ·
                        rfl

theorem cell23_3710164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3710164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710164 prefixEnd_3710164 := by exact prefixLift 3710164
  have htrace : WordTrace (prefixWord ++ tailWord_3710164) baseStart_3710164 baseEnd_3710164 := by
    simpa [prefixWord, tailWord_3710164, baseEnd_3710164] using wordTrace_append hprefix tailTrace_3710164
  have hstable : (prefixWord ++ tailWord_3710164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710164).length < 2 ^ (prefixWord ++ tailWord_3710164).sum := by decide
  have hdescent : baseEnd_3710164 < baseStart_3710164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710199 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_3710199 : Nat := 118140960795 + 3710199 * 2 ^ 59
def prefixEnd_3710199 : Nat := 4983230072969 + 3 ^ 40 * 3710199 * 2
def baseEnd_3710199 : Nat := 1905115410830834563049611

theorem tailTrace_3710199 : CollatzResearch.WordTrace tailWord_3710199 prefixEnd_3710199 1905115410830834563049611 := by
  unfold tailWord_3710199
  simp only [CollatzResearch.WordTrace]
  refine ⟨135322074685590149386733651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90214716457060099591155767 135322074685590149386733651)
  ·
    refine ⟨202983112028385224080100477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135322074685590149386733651 202983112028385224080100477)
    ·
      refine ⟨76118667010644459030037679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202983112028385224080100477 76118667010644459030037679)
      ·
        refine ⟨114178000515966688545056519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76118667010644459030037679 114178000515966688545056519)
        ·
          refine ⟨171267000773950032817584779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114178000515966688545056519 171267000773950032817584779)
          ·
            refine ⟨256900501160925049226377169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171267000773950032817584779 256900501160925049226377169)
            ·
              refine ⟨192675375870693786919782877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256900501160925049226377169 192675375870693786919782877)
              ·
                refine ⟨72253265951510170094918579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192675375870693786919782877 72253265951510170094918579)
                ·
                  refine ⟨108379898927265255142377869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72253265951510170094918579 108379898927265255142377869)
                  ·
                    refine ⟨40642462097724470678391701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108379898927265255142377869 40642462097724470678391701)
                    ·
                      refine ⟨1905115410830834563049611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40642462097724470678391701 1905115410830834563049611)
                      ·
                        rfl

theorem cell23_3710199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_3710199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710199 prefixEnd_3710199 := by exact prefixLift 3710199
  have htrace : WordTrace (prefixWord ++ tailWord_3710199) baseStart_3710199 baseEnd_3710199 := by
    simpa [prefixWord, tailWord_3710199, baseEnd_3710199] using wordTrace_append hprefix tailTrace_3710199
  have hstable : (prefixWord ++ tailWord_3710199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710199).length < 2 ^ (prefixWord ++ tailWord_3710199).sum := by decide
  have hdescent : baseEnd_3710199 < baseStart_3710199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710296 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3710296 : Nat := 118140960795 + 3710296 * 2 ^ 59
def prefixEnd_3710296 : Nat := 4983230072969 + 3 ^ 40 * 3710296 * 2
def baseEnd_3710296 : Nat := 1905165218454320683536665

theorem tailTrace_3710296 : CollatzResearch.WordTrace tailWord_3710296 prefixEnd_3710296 1905165218454320683536665 := by
  unfold tailWord_3710296
  simp only [CollatzResearch.WordTrace]
  refine ⟨67662806283119367476507371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90217075044159156635343161 67662806283119367476507371)
  ·
    refine ⟨101494209424679051214761057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67662806283119367476507371 101494209424679051214761057)
    ·
      refine ⟨76120657068509288411070793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101494209424679051214761057 76120657068509288411070793)
      ·
        refine ⟨57090492801381966308303095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76120657068509288411070793 57090492801381966308303095)
        ·
          refine ⟨85635739202072949462454643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57090492801381966308303095 85635739202072949462454643)
          ·
            refine ⟨128453608803109424193681965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85635739202072949462454643 128453608803109424193681965)
            ·
              refine ⟨48170103301166034072630737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128453608803109424193681965 48170103301166034072630737)
              ·
                refine ⟨36127577475874525554473053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48170103301166034072630737 36127577475874525554473053)
                ·
                  refine ⟨13547841553452947082927395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36127577475874525554473053 13547841553452947082927395)
                  ·
                    refine ⟨20321762330179420624391093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13547841553452947082927395 20321762330179420624391093)
                    ·
                      refine ⟨1905165218454320683536665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20321762330179420624391093 1905165218454320683536665)
                      ·
                        rfl

theorem cell23_3710296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3710296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710296 prefixEnd_3710296 := by exact prefixLift 3710296
  have htrace : WordTrace (prefixWord ++ tailWord_3710296) baseStart_3710296 baseEnd_3710296 := by
    simpa [prefixWord, tailWord_3710296, baseEnd_3710296] using wordTrace_append hprefix tailTrace_3710296
  have hstable : (prefixWord ++ tailWord_3710296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710296).length < 2 ^ (prefixWord ++ tailWord_3710296).sum := by decide
  have hdescent : baseEnd_3710296 < baseStart_3710296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710304 : List Nat := [2, 1, 1, 3, 4, 3, 1, 3, 1, 1, 3]
def baseStart_3710304 : Nat := 118140960795 + 3710304 * 2 ^ 59
def prefixEnd_3710304 : Nat := 4983230072969 + 3 ^ 40 * 3710304 * 2
def baseEnd_3710304 : Nat := 1905169326299556652236629

theorem tailTrace_3710304 : CollatzResearch.WordTrace tailWord_3710304 prefixEnd_3710304 1905169326299556652236629 := by
  unfold tailWord_3710304
  simp only [CollatzResearch.WordTrace]
  refine ⟨67662952175104876159652983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90217269566806501546203977 67662952175104876159652983)
  ·
    refine ⟨101494428262657314239479475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67662952175104876159652983 101494428262657314239479475)
    ·
      refine ⟨152241642393985971359219213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101494428262657314239479475 152241642393985971359219213)
      ·
        refine ⟨57090615897744739259707205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152241642393985971359219213 57090615897744739259707205)
        ·
          refine ⟨10704490480827138611195101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57090615897744739259707205 10704490480827138611195101)
          ·
            refine ⟨4014183930310176979198163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10704490480827138611195101 4014183930310176979198163)
            ·
              refine ⟨6021275895465265468797245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014183930310176979198163 6021275895465265468797245)
              ·
                refine ⟨2257978460799474550798967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6021275895465265468797245 2257978460799474550798967)
                ·
                  refine ⟨3386967691199211826198451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2257978460799474550798967 3386967691199211826198451)
                  ·
                    refine ⟨5080451536798817739297677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3386967691199211826198451 5080451536798817739297677)
                    ·
                      refine ⟨1905169326299556652236629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080451536798817739297677 1905169326299556652236629)
                      ·
                        rfl

theorem cell23_3710304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_3710304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710304 prefixEnd_3710304 := by exact prefixLift 3710304
  have htrace : WordTrace (prefixWord ++ tailWord_3710304) baseStart_3710304 baseEnd_3710304 := by
    simpa [prefixWord, tailWord_3710304, baseEnd_3710304] using wordTrace_append hprefix tailTrace_3710304
  have hstable : (prefixWord ++ tailWord_3710304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710304).length < 2 ^ (prefixWord ++ tailWord_3710304).sum := by decide
  have hdescent : baseEnd_3710304 < baseStart_3710304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710316 : List Nat := [2, 2, 1, 1, 5, 1, 11]
def baseStart_3710316 : Nat := 118140960795 + 3710316 * 2 ^ 59
def prefixEnd_3710316 : Nat := 4983230072969 + 3 ^ 40 * 3710316 * 2
def baseEnd_3710316 : Nat := 23520685037869266731933

theorem tailTrace_3710316 : CollatzResearch.WordTrace tailWord_3710316 prefixEnd_3710316 23520685037869266731933 := by
  unfold tailWord_3710316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67663171013083139184371401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90217561350777518912495201 67663171013083139184371401)
  ·
    refine ⟨50747378259812354388278551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67663171013083139184371401 50747378259812354388278551)
    ·
      refine ⟨76121067389718531582417827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50747378259812354388278551 76121067389718531582417827)
      ·
        refine ⟨114181601084577797373626741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76121067389718531582417827 114181601084577797373626741)
        ·
          refine ⟨10704525101679168503777507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114181601084577797373626741 10704525101679168503777507)
          ·
            refine ⟨16056787652518752755666261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10704525101679168503777507 16056787652518752755666261)
            ·
              refine ⟨23520685037869266731933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16056787652518752755666261 23520685037869266731933)
              ·
                rfl

theorem cell23_3710316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 11].length) (baseStart_3710316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710316 prefixEnd_3710316 := by exact prefixLift 3710316
  have htrace : WordTrace (prefixWord ++ tailWord_3710316) baseStart_3710316 baseEnd_3710316 := by
    simpa [prefixWord, tailWord_3710316, baseEnd_3710316] using wordTrace_append hprefix tailTrace_3710316
  have hstable : (prefixWord ++ tailWord_3710316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710316).length < 2 ^ (prefixWord ++ tailWord_3710316).sum := by decide
  have hdescent : baseEnd_3710316 < baseStart_3710316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710337 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3710337 : Nat := 118140960795 + 3710337 * 2 ^ 59
def prefixEnd_3710337 : Nat := 4983230072969 + 3 ^ 40 * 3710337 * 2
def baseEnd_3710337 : Nat := 635062090387051674374659

theorem tailTrace_3710337 : CollatzResearch.WordTrace tailWord_3710337 prefixEnd_3710337 635062090387051674374659 := by
  unfold tailWord_3710337
  simp only [CollatzResearch.WordTrace]
  refine ⟨135327107959090198955257265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90218071972726799303504843 135327107959090198955257265)
  ·
    refine ⟨101495330969317649216442949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135327107959090198955257265 101495330969317649216442949)
    ·
      refine ⟨19030374556747059228083053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101495330969317649216442949 19030374556747059228083053)
      ·
        refine ⟨7136390458780147210531145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19030374556747059228083053 7136390458780147210531145)
        ·
          refine ⟨5352292844085110407898359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7136390458780147210531145 5352292844085110407898359)
          ·
            refine ⟨8028439266127665611847539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352292844085110407898359 8028439266127665611847539)
            ·
              refine ⟨12042658899191498417771309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8028439266127665611847539 12042658899191498417771309)
              ·
                refine ⟨4515997087196811906664241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12042658899191498417771309 4515997087196811906664241)
                ·
                  refine ⟨3386997815397608929998181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515997087196811906664241 3386997815397608929998181)
                  ·
                    refine ⟨635062090387051674374659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3386997815397608929998181 635062090387051674374659)
                    ·
                      rfl

theorem cell23_3710337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3710337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710337 prefixEnd_3710337 := by exact prefixLift 3710337
  have htrace : WordTrace (prefixWord ++ tailWord_3710337) baseStart_3710337 baseEnd_3710337 := by
    simpa [prefixWord, tailWord_3710337, baseEnd_3710337] using wordTrace_append hprefix tailTrace_3710337
  have hstable : (prefixWord ++ tailWord_3710337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710337).length < 2 ^ (prefixWord ++ tailWord_3710337).sum := by decide
  have hdescent : baseEnd_3710337 < baseStart_3710337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710353 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 7, 2]
def baseStart_3710353 : Nat := 118140960795 + 3710353 * 2 ^ 59
def prefixEnd_3710353 : Nat := 4983230072969 + 3 ^ 40 * 3710353 * 2
def baseEnd_3710353 : Nat := 1905194486851626960523903

theorem tailTrace_3710353 : CollatzResearch.WordTrace tailWord_3710353 prefixEnd_3710353 1905194486851626960523903 := by
  unfold tailWord_3710353
  simp only [CollatzResearch.WordTrace]
  refine ⟨135327691527032233687839713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90218461018021489125226475 135327691527032233687839713)
  ·
    refine ⟨101495768645274175265879785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135327691527032233687839713 101495768645274175265879785)
    ·
      refine ⟨76121826483955631449409839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101495768645274175265879785 76121826483955631449409839)
      ·
        refine ⟨114182739725933447174114759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76121826483955631449409839 114182739725933447174114759)
        ·
          refine ⟨171274109588900170761172139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114182739725933447174114759 171274109588900170761172139)
          ·
            refine ⟨256911164383350256141758209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171274109588900170761172139 256911164383350256141758209)
            ·
              refine ⟨192683373287512692106318657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256911164383350256141758209 192683373287512692106318657)
              ·
                refine ⟨144512529965634519079738993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192683373287512692106318657 144512529965634519079738993)
                ·
                  refine ⟨108384397474225889309804245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144512529965634519079738993 108384397474225889309804245)
                  ·
                    refine ⟨2540259315802169280698537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 108384397474225889309804245 2540259315802169280698537)
                    ·
                      refine ⟨1905194486851626960523903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540259315802169280698537 1905194486851626960523903)
                      ·
                        rfl

theorem cell23_3710353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_3710353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710353 prefixEnd_3710353 := by exact prefixLift 3710353
  have htrace : WordTrace (prefixWord ++ tailWord_3710353) baseStart_3710353 baseEnd_3710353 := by
    simpa [prefixWord, tailWord_3710353, baseEnd_3710353] using wordTrace_append hprefix tailTrace_3710353
  have hstable : (prefixWord ++ tailWord_3710353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710353).length < 2 ^ (prefixWord ++ tailWord_3710353).sum := by decide
  have hdescent : baseEnd_3710353 < baseStart_3710353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710364 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3710364 : Nat := 118140960795 + 3710364 * 2 ^ 59
def prefixEnd_3710364 : Nat := 4983230072969 + 3 ^ 40 * 3710364 * 2
def baseEnd_3710364 : Nat := 1905200135138826417486353

theorem tailTrace_3710364 : CollatzResearch.WordTrace tailWord_3710364 prefixEnd_3710364 1905200135138826417486353 := by
  unfold tailWord_3710364
  simp only [CollatzResearch.WordTrace]
  refine ⟨67664046364996191283245073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90218728486661588377660097 67664046364996191283245073)
  ·
    refine ⟨50748034773747143462433805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67664046364996191283245073 50748034773747143462433805)
    ·
      refine ⟨19030513040155178798412677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50748034773747143462433805 19030513040155178798412677)
      ·
        refine ⟨3568221195029096024702377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19030513040155178798412677 3568221195029096024702377)
        ·
          refine ⟨2676165896271822018526783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3568221195029096024702377 2676165896271822018526783)
          ·
            refine ⟨4014248844407733027790175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676165896271822018526783 4014248844407733027790175)
            ·
              refine ⟨6021373266611599541685263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014248844407733027790175 6021373266611599541685263)
              ·
                refine ⟨9032059899917399312527895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021373266611599541685263 9032059899917399312527895)
                ·
                  refine ⟨13548089849876098968791843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032059899917399312527895 13548089849876098968791843)
                  ·
                    refine ⟨20322134774814148453187765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13548089849876098968791843 20322134774814148453187765)
                    ·
                      refine ⟨1905200135138826417486353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20322134774814148453187765 1905200135138826417486353)
                      ·
                        rfl

theorem cell23_3710364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3710364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710364 prefixEnd_3710364 := by exact prefixLift 3710364
  have htrace : WordTrace (prefixWord ++ tailWord_3710364) baseStart_3710364 baseEnd_3710364 := by
    simpa [prefixWord, tailWord_3710364, baseEnd_3710364] using wordTrace_append hprefix tailTrace_3710364
  have hstable : (prefixWord ++ tailWord_3710364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710364).length < 2 ^ (prefixWord ++ tailWord_3710364).sum := by decide
  have hdescent : baseEnd_3710364 < baseStart_3710364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710400 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 1, 4, 2]
def baseStart_3710400 : Nat := 118140960795 + 3710400 * 2 ^ 59
def prefixEnd_3710400 : Nat := 4983230072969 + 3 ^ 40 * 3710400 * 2
def baseEnd_3710400 : Nat := 1905218620442388276636187

theorem tailTrace_3710400 : CollatzResearch.WordTrace tailWord_3710400 prefixEnd_3710400 1905218620442388276636187 := by
  unfold tailWord_3710400
  simp only [CollatzResearch.WordTrace]
  refine ⟨67664702878930980357400327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90219603838574640476533769 67664702878930980357400327)
  ·
    refine ⟨101497054318396470536100491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67664702878930980357400327 101497054318396470536100491)
    ·
      refine ⟨152245581477594705804150737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101497054318396470536100491 152245581477594705804150737)
      ·
        refine ⟨114184186108196029353113053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152245581477594705804150737 114184186108196029353113053)
        ·
          refine ⟨42819069790573511007417395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114184186108196029353113053 42819069790573511007417395)
          ·
            refine ⟨64228604685860266511126093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42819069790573511007417395 64228604685860266511126093)
            ·
              refine ⟨24085726757197599941672285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64228604685860266511126093 24085726757197599941672285)
              ·
                refine ⟨9032147533949099978127107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24085726757197599941672285 9032147533949099978127107)
                ·
                  refine ⟨13548221300923649967190661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032147533949099978127107 13548221300923649967190661)
                  ·
                    refine ⟨2540291493923184368848249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13548221300923649967190661 2540291493923184368848249)
                    ·
                      refine ⟨1905218620442388276636187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540291493923184368848249 1905218620442388276636187)
                      ·
                        rfl

theorem cell23_3710400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_3710400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710400 prefixEnd_3710400 := by exact prefixLift 3710400
  have htrace : WordTrace (prefixWord ++ tailWord_3710400) baseStart_3710400 baseEnd_3710400 := by
    simpa [prefixWord, tailWord_3710400, baseEnd_3710400] using wordTrace_append hprefix tailTrace_3710400
  have hstable : (prefixWord ++ tailWord_3710400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710400).length < 2 ^ (prefixWord ++ tailWord_3710400).sum := by decide
  have hdescent : baseEnd_3710400 < baseStart_3710400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710440 : List Nat := [2, 1, 4, 1, 1, 2, 1, 6, 5]
def baseStart_3710440 : Nat := 118140960795 + 3710440 * 2 ^ 59
def prefixEnd_3710440 : Nat := 4983230072969 + 3 ^ 40 * 3710440 * 2
def baseEnd_3710440 : Nat := 211693239963174235570667

theorem tailTrace_3710440 : CollatzResearch.WordTrace tailWord_3710440 prefixEnd_3710440 211693239963174235570667 := by
  unfold tailWord_3710440
  simp only [CollatzResearch.WordTrace]
  refine ⟨67665432338858523773128387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90220576451811365030837849 67665432338858523773128387)
  ·
    refine ⟨101498148508287785659692581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67665432338858523773128387 101498148508287785659692581)
    ·
      refine ⟨19030902845303959811192359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101498148508287785659692581 19030902845303959811192359)
      ·
        refine ⟨28546354267955939716788539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19030902845303959811192359 28546354267955939716788539)
        ·
          refine ⟨42819531401933909575182809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28546354267955939716788539 42819531401933909575182809)
          ·
            refine ⟨32114648551450432181387107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42819531401933909575182809 32114648551450432181387107)
            ·
              refine ⟨48171972827175648272080661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32114648551450432181387107 48171972827175648272080661)
              ·
                refine ⟨2258061226273858512753781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48171972827175648272080661 2258061226273858512753781)
                ·
                  refine ⟨211693239963174235570667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2258061226273858512753781 211693239963174235570667)
                  ·
                    rfl

theorem cell23_3710440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 5].length) (baseStart_3710440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710440 prefixEnd_3710440 := by exact prefixLift 3710440
  have htrace : WordTrace (prefixWord ++ tailWord_3710440) baseStart_3710440 baseEnd_3710440 := by
    simpa [prefixWord, tailWord_3710440, baseEnd_3710440] using wordTrace_append hprefix tailTrace_3710440
  have hstable : (prefixWord ++ tailWord_3710440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710440).length < 2 ^ (prefixWord ++ tailWord_3710440).sum := by decide
  have hdescent : baseEnd_3710440 < baseStart_3710440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710460 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_3710460 : Nat := 118140960795 + 3710460 * 2 ^ 59
def prefixEnd_3710460 : Nat := 4983230072969 + 3 ^ 40 * 3710460 * 2
def baseEnd_3710460 : Nat := 1905249429281658041885911

theorem tailTrace_3710460 : CollatzResearch.WordTrace tailWord_3710460 prefixEnd_3710460 1905249429281658041885911 := by
  unfold tailWord_3710460
  simp only [CollatzResearch.WordTrace]
  refine ⟨67665797068822295480992417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90221062758429727307989889 67665797068822295480992417)
  ·
    refine ⟨50749347801616721610744313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67665797068822295480992417 50749347801616721610744313)
    ·
      refine ⟨38062010851212541208058235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50749347801616721610744313 38062010851212541208058235)
      ·
        refine ⟨57093016276818811812087353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38062010851212541208058235 57093016276818811812087353)
        ·
          refine ⟨42819762207614108859065515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57093016276818811812087353 42819762207614108859065515)
          ·
            refine ⟨64229643311421163288598273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42819762207614108859065515 64229643311421163288598273)
            ·
              refine ⟨48172232483565872466448705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64229643311421163288598273 48172232483565872466448705)
              ·
                refine ⟨36129174362674404349836529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48172232483565872466448705 36129174362674404349836529)
                ·
                  refine ⟨27096880772005803262377397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36129174362674404349836529 27096880772005803262377397)
                  ·
                    refine ⟨2540332572375544055847881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27096880772005803262377397 2540332572375544055847881)
                    ·
                      refine ⟨1905249429281658041885911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540332572375544055847881 1905249429281658041885911)
                      ·
                        rfl

theorem cell23_3710460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_3710460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710460 prefixEnd_3710460 := by exact prefixLift 3710460
  have htrace : WordTrace (prefixWord ++ tailWord_3710460) baseStart_3710460 baseEnd_3710460 := by
    simpa [prefixWord, tailWord_3710460, baseEnd_3710460] using wordTrace_append hprefix tailTrace_3710460
  have hstable : (prefixWord ++ tailWord_3710460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710460).length < 2 ^ (prefixWord ++ tailWord_3710460).sum := by decide
  have hdescent : baseEnd_3710460 < baseStart_3710460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710473 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_3710473 : Nat := 118140960795 + 3710473 * 2 ^ 59
def prefixEnd_3710473 : Nat := 4983230072969 + 3 ^ 40 * 3710473 * 2
def baseEnd_3710473 : Nat := 1905256104530166491023351

theorem tailTrace_3710473 : CollatzResearch.WordTrace tailWord_3710473 prefixEnd_3710473 1905256104530166491023351 := by
  unfold tailWord_3710473
  simp only [CollatzResearch.WordTrace]
  refine ⟨135332068286597494182208073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90221378857731662788138715 135332068286597494182208073)
  ·
    refine ⟨101499051214948120636656055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135332068286597494182208073 101499051214948120636656055)
    ·
      refine ⟨152248576822422180954984083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101499051214948120636656055 152248576822422180954984083)
      ·
        refine ⟨228372865233633271432476125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152248576822422180954984083 228372865233633271432476125)
        ·
          refine ⟨85639824462612476787178547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228372865233633271432476125 85639824462612476787178547)
          ·
            refine ⟨128459736693918715180767821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85639824462612476787178547 128459736693918715180767821)
            ·
              refine ⟨48172401260219518192787933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128459736693918715180767821 48172401260219518192787933)
              ·
                refine ⟨18064650472582319322295475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48172401260219518192787933 18064650472582319322295475)
                ·
                  refine ⟨27096975708873478983443213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18064650472582319322295475 27096975708873478983443213)
                  ·
                    refine ⟨10161365890827554618791205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27096975708873478983443213 10161365890827554618791205)
                    ·
                      refine ⟨1905256104530166491023351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10161365890827554618791205 1905256104530166491023351)
                      ·
                        rfl

theorem cell23_3710473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_3710473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710473 prefixEnd_3710473 := by exact prefixLift 3710473
  have htrace : WordTrace (prefixWord ++ tailWord_3710473) baseStart_3710473 baseEnd_3710473 := by
    simpa [prefixWord, tailWord_3710473, baseEnd_3710473] using wordTrace_append hprefix tailTrace_3710473
  have hstable : (prefixWord ++ tailWord_3710473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710473).length < 2 ^ (prefixWord ++ tailWord_3710473).sum := by decide
  have hdescent : baseEnd_3710473 < baseStart_3710473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710527 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 3]
def baseStart_3710527 : Nat := 118140960795 + 3710527 * 2 ^ 59
def prefixEnd_3710527 : Nat := 4983230072969 + 3 ^ 40 * 3710527 * 2
def baseEnd_3710527 : Nat := 1905283832485509279748103

theorem tailTrace_3710527 : CollatzResearch.WordTrace tailWord_3710527 prefixEnd_3710527 1905283832485509279748103 := by
  unfold tailWord_3710527
  simp only [CollatzResearch.WordTrace]
  refine ⟨135334037828401861404673835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90222691885601240936449223 135334037828401861404673835)
  ·
    refine ⟨203001056742602792107010753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135334037828401861404673835 203001056742602792107010753)
    ·
      refine ⟨152250792556952094080258065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203001056742602792107010753 152250792556952094080258065)
      ·
        refine ⟨114188094417714070560193549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152250792556952094080258065 114188094417714070560193549)
        ·
          refine ⟨42820535406642776460072581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114188094417714070560193549 42820535406642776460072581)
          ·
            refine ⟨8028850388745520586263609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42820535406642776460072581 8028850388745520586263609)
            ·
              refine ⟨6021637791559140439697707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8028850388745520586263609 6021637791559140439697707)
              ·
                refine ⟨9032456687338710659546561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021637791559140439697707 9032456687338710659546561)
                ·
                  refine ⟨6774342515504032994659921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9032456687338710659546561 6774342515504032994659921)
                  ·
                    refine ⟨5080756886628024745994941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6774342515504032994659921 5080756886628024745994941)
                    ·
                      refine ⟨1905283832485509279748103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080756886628024745994941 1905283832485509279748103)
                      ·
                        rfl

theorem cell23_3710527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_3710527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710527 prefixEnd_3710527 := by exact prefixLift 3710527
  have htrace : WordTrace (prefixWord ++ tailWord_3710527) baseStart_3710527 baseEnd_3710527 := by
    simpa [prefixWord, tailWord_3710527, baseEnd_3710527] using wordTrace_append hprefix tailTrace_3710527
  have hstable : (prefixWord ++ tailWord_3710527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710527).length < 2 ^ (prefixWord ++ tailWord_3710527).sum := by decide
  have hdescent : baseEnd_3710527 < baseStart_3710527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710551 : List Nat := [1, 1, 3, 2, 2, 5, 2, 2, 1, 4]
def baseStart_3710551 : Nat := 118140960795 + 3710551 * 2 ^ 59
def prefixEnd_3710551 : Nat := 4983230072969 + 3 ^ 40 * 3710551 * 2
def baseEnd_3710551 : Nat := 635098718673739061949331

theorem tailTrace_3710551 : CollatzResearch.WordTrace tailWord_3710551 prefixEnd_3710551 635098718673739061949331 := by
  unfold tailWord_3710551
  simp only [CollatzResearch.WordTrace]
  refine ⟨135334913180314913503547507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90223275453543275669031671 135334913180314913503547507)
  ·
    refine ⟨203002369770472370255321261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135334913180314913503547507 203002369770472370255321261)
    ·
      refine ⟨76125888663927138845745473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203002369770472370255321261 76125888663927138845745473)
      ·
        refine ⟨57094416497945354134309105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76125888663927138845745473 57094416497945354134309105)
        ·
          refine ⟨42820812373459015600731829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57094416497945354134309105 42820812373459015600731829)
          ·
            refine ⟨4014451160011782712568609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42820812373459015600731829 4014451160011782712568609)
            ·
              refine ⟨3010838370008837034426457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014451160011782712568609 3010838370008837034426457)
              ·
                refine ⟨2258128777506627775819843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010838370008837034426457 2258128777506627775819843)
                ·
                  refine ⟨3387193166259941663729765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258128777506627775819843 3387193166259941663729765)
                  ·
                    refine ⟨635098718673739061949331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3387193166259941663729765 635098718673739061949331)
                    ·
                      rfl

theorem cell23_3710551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_3710551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710551 prefixEnd_3710551 := by exact prefixLift 3710551
  have htrace : WordTrace (prefixWord ++ tailWord_3710551) baseStart_3710551 baseEnd_3710551 := by
    simpa [prefixWord, tailWord_3710551, baseEnd_3710551] using wordTrace_append hprefix tailTrace_3710551
  have hstable : (prefixWord ++ tailWord_3710551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710551).length < 2 ^ (prefixWord ++ tailWord_3710551).sum := by decide
  have hdescent : baseEnd_3710551 < baseStart_3710551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710553 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_3710553 : Nat := 118140960795 + 3710553 * 2 ^ 59
def prefixEnd_3710553 : Nat := 4983230072969 + 3 ^ 40 * 3710553 * 2
def baseEnd_3710553 : Nat := 1905297182982526178022983

theorem tailTrace_3710553 : CollatzResearch.WordTrace tailWord_3710553 prefixEnd_3710553 1905297182982526178022983 := by
  unfold tailWord_3710553
  simp only [CollatzResearch.WordTrace]
  refine ⟨135334986126307667845120313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90223324084205111896746875 135334986126307667845120313)
  ·
    refine ⟨101501239594730750883840235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135334986126307667845120313 101501239594730750883840235)
    ·
      refine ⟨152251859392096126325760353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101501239594730750883840235 152251859392096126325760353)
      ·
        refine ⟨114188894544072094744320265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152251859392096126325760353 114188894544072094744320265)
        ·
          refine ⟨85641670908054071058240199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114188894544072094744320265 85641670908054071058240199)
          ·
            refine ⟨128462506362081106587360299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85641670908054071058240199 128462506362081106587360299)
            ·
              refine ⟨192693759543121659881040449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128462506362081106587360299 192693759543121659881040449)
              ·
                refine ⟨144520319657341244910780337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192693759543121659881040449 144520319657341244910780337)
                ·
                  refine ⟨108390239743005933683085253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144520319657341244910780337 108390239743005933683085253)
                  ·
                    refine ⟨20323169951813612565578485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108390239743005933683085253 20323169951813612565578485)
                    ·
                      refine ⟨1905297182982526178022983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20323169951813612565578485 1905297182982526178022983)
                      ·
                        rfl

theorem cell23_3710553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_3710553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710553 prefixEnd_3710553 := by exact prefixLift 3710553
  have htrace : WordTrace (prefixWord ++ tailWord_3710553) baseStart_3710553 baseEnd_3710553 := by
    simpa [prefixWord, tailWord_3710553, baseEnd_3710553] using wordTrace_append hprefix tailTrace_3710553
  have hstable : (prefixWord ++ tailWord_3710553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710553).length < 2 ^ (prefixWord ++ tailWord_3710553).sum := by decide
  have hdescent : baseEnd_3710553 < baseStart_3710553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710567 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_3710567 : Nat := 118140960795 + 3710567 * 2 ^ 59
def prefixEnd_3710567 : Nat := 4983230072969 + 3 ^ 40 * 3710567 * 2
def baseEnd_3710567 : Nat := 1905304371711689123247919

theorem tailTrace_3710567 : CollatzResearch.WordTrace tailWord_3710567 prefixEnd_3710567 1905304371711689123247919 := by
  unfold tailWord_3710567
  simp only [CollatzResearch.WordTrace]
  refine ⟨135335496748256948236129955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90223664498837965490753303 135335496748256948236129955)
  ·
    refine ⟨203003245122385422354194933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135335496748256948236129955 203003245122385422354194933)
    ·
      refine ⟨19031554230223633345705775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203003245122385422354194933 19031554230223633345705775)
      ·
        refine ⟨28547331345335450018558663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19031554230223633345705775 28547331345335450018558663)
        ·
          refine ⟨42820997018003175027837995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28547331345335450018558663 42820997018003175027837995)
          ·
            refine ⟨64231495527004762541756993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42820997018003175027837995 64231495527004762541756993)
            ·
              refine ⟨48173621645253571906317745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64231495527004762541756993 48173621645253571906317745)
              ·
                refine ⟨36130216233940178929738309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48173621645253571906317745 36130216233940178929738309)
                ·
                  refine ⟨6774415543863783549325933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36130216233940178929738309 6774415543863783549325933)
                  ·
                    refine ⟨2540405828948918830997225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6774415543863783549325933 2540405828948918830997225)
                    ·
                      refine ⟨1905304371711689123247919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540405828948918830997225 1905304371711689123247919)
                      ·
                        rfl

theorem cell23_3710567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_3710567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710567 prefixEnd_3710567 := by exact prefixLift 3710567
  have htrace : WordTrace (prefixWord ++ tailWord_3710567) baseStart_3710567 baseEnd_3710567 := by
    simpa [prefixWord, tailWord_3710567, baseEnd_3710567] using wordTrace_append hprefix tailTrace_3710567
  have hstable : (prefixWord ++ tailWord_3710567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710567).length < 2 ^ (prefixWord ++ tailWord_3710567).sum := by decide
  have hdescent : baseEnd_3710567 < baseStart_3710567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710597 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_3710597 : Nat := 118140960795 + 3710597 * 2 ^ 59
def prefixEnd_3710597 : Nat := 4983230072969 + 3 ^ 40 * 3710597 * 2
def baseEnd_3710597 : Nat := 1905319776131324005872781

theorem tailTrace_3710597 : CollatzResearch.WordTrace tailWord_3710597 prefixEnd_3710597 1905319776131324005872781 := by
  unfold tailWord_3710597
  simp only [CollatzResearch.WordTrace]
  refine ⟨135336590938148263359722045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90224393958765508906481363 135336590938148263359722045)
  ·
    refine ⟨50751221601805598759895767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135336590938148263359722045 50751221601805598759895767)
    ·
      refine ⟨76126832402708398139843651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50751221601805598759895767 76126832402708398139843651)
      ·
        refine ⟨114190248604062597209765477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76126832402708398139843651 114190248604062597209765477)
        ·
          refine ⟨21410671613261736976831027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114190248604062597209765477 21410671613261736976831027)
          ·
            refine ⟨32116007419892605465246541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21410671613261736976831027 32116007419892605465246541)
            ·
              refine ⟨12043502782459727049467453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32116007419892605465246541 12043502782459727049467453)
              ·
                refine ⟨4516313543422397643550295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12043502782459727049467453 4516313543422397643550295)
                ·
                  refine ⟨6774470315133596465325443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516313543422397643550295 6774470315133596465325443)
                  ·
                    refine ⟨10161705472700394697988165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6774470315133596465325443 10161705472700394697988165)
                    ·
                      refine ⟨1905319776131324005872781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10161705472700394697988165 1905319776131324005872781)
                      ·
                        rfl

theorem cell23_3710597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_3710597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710597 prefixEnd_3710597 := by exact prefixLift 3710597
  have htrace : WordTrace (prefixWord ++ tailWord_3710597) baseStart_3710597 baseEnd_3710597 := by
    simpa [prefixWord, tailWord_3710597, baseEnd_3710597] using wordTrace_append hprefix tailTrace_3710597
  have hstable : (prefixWord ++ tailWord_3710597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710597).length < 2 ^ (prefixWord ++ tailWord_3710597).sum := by decide
  have hdescent : baseEnd_3710597 < baseStart_3710597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710603 : List Nat := [1, 1, 1, 1, 4, 1, 14]
def baseStart_3710603 : Nat := 118140960795 + 3710603 * 2 ^ 59
def prefixEnd_3710603 : Nat := 4983230072969 + 3 ^ 40 * 3710603 * 2
def baseEnd_3710603 : Nat := 23522504407595691140713

theorem tailTrace_3710603 : CollatzResearch.WordTrace tailWord_3710603 prefixEnd_3710603 23522504407595691140713 := by
  unfold tailWord_3710603
  simp only [CollatzResearch.WordTrace]
  refine ⟨135336809776126526384440463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90224539850751017589626975 135336809776126526384440463)
  ·
    refine ⟨203005214664189789576660695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135336809776126526384440463 203005214664189789576660695)
    ·
      refine ⟨304507821996284684364991043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203005214664189789576660695 304507821996284684364991043)
      ·
        refine ⟨456761732994427026547486565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304507821996284684364991043 456761732994427026547486565)
        ·
          refine ⟨85642824936455067477653731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456761732994427026547486565 85642824936455067477653731)
          ·
            refine ⟨128464237404682601216480597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85642824936455067477653731 128464237404682601216480597)
            ·
              refine ⟨23522504407595691140713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 128464237404682601216480597 23522504407595691140713)
              ·
                rfl

theorem cell23_3710603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 14].length) (baseStart_3710603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710603 prefixEnd_3710603 := by exact prefixLift 3710603
  have htrace : WordTrace (prefixWord ++ tailWord_3710603) baseStart_3710603 baseEnd_3710603 := by
    simpa [prefixWord, tailWord_3710603, baseEnd_3710603] using wordTrace_append hprefix tailTrace_3710603
  have hstable : (prefixWord ++ tailWord_3710603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710603).length < 2 ^ (prefixWord ++ tailWord_3710603).sum := by decide
  have hdescent : baseEnd_3710603 < baseStart_3710603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710664 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_3710664 : Nat := 118140960795 + 3710664 * 2 ^ 59
def prefixEnd_3710664 : Nat := 4983230072969 + 3 ^ 40 * 3710664 * 2
def baseEnd_3710664 : Nat := 1905354179335175243734973

theorem tailTrace_3710664 : CollatzResearch.WordTrace tailWord_3710664 prefixEnd_3710664 1905354179335175243734973 := by
  unfold tailWord_3710664
  simp only [CollatzResearch.WordTrace]
  refine ⟨67669517314452766901205523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90226023085937022534940697 67669517314452766901205523)
  ·
    refine ⟨101504275971679150351808285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67669517314452766901205523 101504275971679150351808285)
    ·
      refine ⟨38064103489379681381928107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101504275971679150351808285 38064103489379681381928107)
      ·
        refine ⟨57096155234069522072892161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38064103489379681381928107 57096155234069522072892161)
        ·
          refine ⟨42822116425552141554669121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57096155234069522072892161 42822116425552141554669121)
          ·
            refine ⟨32116587319164106166001841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42822116425552141554669121 32116587319164106166001841)
            ·
              refine ⟨24087440489373079624501381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32116587319164106166001841 24087440489373079624501381)
              ·
                refine ⟨4516395091757452429594009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24087440489373079624501381 4516395091757452429594009)
                ·
                  refine ⟨3387296318818089322195507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516395091757452429594009 3387296318818089322195507)
                  ·
                    refine ⟨5080944478227133983293261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3387296318818089322195507 5080944478227133983293261)
                    ·
                      refine ⟨1905354179335175243734973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080944478227133983293261 1905354179335175243734973)
                      ·
                        rfl

theorem cell23_3710664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_3710664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710664 prefixEnd_3710664 := by exact prefixLift 3710664
  have htrace : WordTrace (prefixWord ++ tailWord_3710664) baseStart_3710664 baseEnd_3710664 := by
    simpa [prefixWord, tailWord_3710664, baseEnd_3710664] using wordTrace_append hprefix tailTrace_3710664
  have hstable : (prefixWord ++ tailWord_3710664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710664).length < 2 ^ (prefixWord ++ tailWord_3710664).sum := by decide
  have hdescent : baseEnd_3710664 < baseStart_3710664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710680 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 1, 8]
def baseStart_3710680 : Nat := 118140960795 + 3710680 * 2 ^ 59
def prefixEnd_3710680 : Nat := 4983230072969 + 3 ^ 40 * 3710680 * 2
def baseEnd_3710680 : Nat := 635120798341882393711633

theorem tailTrace_3710680 : CollatzResearch.WordTrace tailWord_3710680 prefixEnd_3710680 635120798341882393711633 := by
  unfold tailWord_3710680
  simp only [CollatzResearch.WordTrace]
  refine ⟨67669809098423784267496747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90226412131231712356662329 67669809098423784267496747)
  ·
    refine ⟨101504713647635676401245121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67669809098423784267496747 101504713647635676401245121)
    ·
      refine ⟨76128535235726757300933841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101504713647635676401245121 76128535235726757300933841)
      ·
        refine ⟨57096401426795067975700381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76128535235726757300933841 57096401426795067975700381)
        ·
          refine ⟨21411150535048150490887643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57096401426795067975700381 21411150535048150490887643)
          ·
            refine ⟨32116725802572225736331465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21411150535048150490887643 32116725802572225736331465)
            ·
              refine ⟨24087544351929169302248599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32116725802572225736331465 24087544351929169302248599)
              ·
                refine ⟨36131316527893753953372899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24087544351929169302248599 36131316527893753953372899)
                ·
                  refine ⟨54196974791840630930059349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36131316527893753953372899 54196974791840630930059349)
                  ·
                    refine ⟨635120798341882393711633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54196974791840630930059349 635120798341882393711633)
                    ·
                      rfl

theorem cell23_3710680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_3710680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710680 prefixEnd_3710680 := by exact prefixLift 3710680
  have htrace : WordTrace (prefixWord ++ tailWord_3710680) baseStart_3710680 baseEnd_3710680 := by
    simpa [prefixWord, tailWord_3710680, baseEnd_3710680] using wordTrace_append hprefix tailTrace_3710680
  have hstable : (prefixWord ++ tailWord_3710680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710680).length < 2 ^ (prefixWord ++ tailWord_3710680).sum := by decide
  have hdescent : baseEnd_3710680 < baseStart_3710680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710681 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 2, 1, 3]
def baseStart_3710681 : Nat := 118140960795 + 3710681 * 2 ^ 59
def prefixEnd_3710681 : Nat := 4983230072969 + 3 ^ 40 * 3710681 * 2
def baseEnd_3710681 : Nat := 1905362908506301677222395

theorem tailTrace_3710681 : CollatzResearch.WordTrace tailWord_3710681 prefixEnd_3710681 1905362908506301677222395 := by
  unfold tailWord_3710681
  simp only [CollatzResearch.WordTrace]
  refine ⟨135339654669843945705779897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90226436446562630470519931 135339654669843945705779897)
  ·
    refine ⟨101504741002382959279334923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135339654669843945705779897 101504741002382959279334923)
    ·
      refine ⟨152257111503574438919002385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101504741002382959279334923 152257111503574438919002385)
      ·
        refine ⟨114192833627680829189251789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152257111503574438919002385 114192833627680829189251789)
        ·
          refine ⟨42822312610380310945969421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114192833627680829189251789 42822312610380310945969421)
          ·
            refine ⟨16058367228892616604738533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42822312610380310945969421 16058367228892616604738533)
            ·
              refine ⟨3010943855417365613388475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16058367228892616604738533 3010943855417365613388475)
              ·
                refine ⟨4516415783126048420082713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010943855417365613388475 4516415783126048420082713)
                ·
                  refine ⟨3387311837344536315062035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516415783126048420082713 3387311837344536315062035)
                  ·
                    refine ⟨5080967756016804472593053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3387311837344536315062035 5080967756016804472593053)
                    ·
                      refine ⟨1905362908506301677222395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080967756016804472593053 1905362908506301677222395)
                      ·
                        rfl

theorem cell23_3710681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_3710681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710681 prefixEnd_3710681 := by exact prefixLift 3710681
  have htrace : WordTrace (prefixWord ++ tailWord_3710681) baseStart_3710681 baseEnd_3710681 := by
    simpa [prefixWord, tailWord_3710681, baseEnd_3710681] using wordTrace_append hprefix tailTrace_3710681
  have hstable : (prefixWord ++ tailWord_3710681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710681).length < 2 ^ (prefixWord ++ tailWord_3710681).sum := by decide
  have hdescent : baseEnd_3710681 < baseStart_3710681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710685 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3710685 : Nat := 118140960795 + 3710685 * 2 ^ 59
def prefixEnd_3710685 : Nat := 4983230072969 + 3 ^ 40 * 3710685 * 2
def baseEnd_3710685 : Nat := 1905364962428919661572377

theorem tailTrace_3710685 : CollatzResearch.WordTrace tailWord_3710685 prefixEnd_3710685 1905364962428919661572377 := by
  unfold tailWord_3710685
  simp only [CollatzResearch.WordTrace]
  refine ⟨135339800561829454388925509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90226533707886302925950339 135339800561829454388925509)
  ·
    refine ⟨25376212605343022697923533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135339800561829454388925509 25376212605343022697923533)
    ·
      refine ⟨9516079727003633511721325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25376212605343022697923533 9516079727003633511721325)
      ·
        refine ⟨3568529897626362566895497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9516079727003633511721325 3568529897626362566895497)
        ·
          refine ⟨2676397423219771925171623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3568529897626362566895497 2676397423219771925171623)
          ·
            refine ⟨4014596134829657887757435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676397423219771925171623 4014596134829657887757435)
            ·
              refine ⟨6021894202244486831636153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014596134829657887757435 6021894202244486831636153)
              ·
                refine ⟨4516420651683365123727115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6021894202244486831636153 4516420651683365123727115)
                ·
                  refine ⟨6774630977525047685590673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516420651683365123727115 6774630977525047685590673)
                  ·
                    refine ⟨5080973233143785764193005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6774630977525047685590673 5080973233143785764193005)
                    ·
                      refine ⟨1905364962428919661572377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5080973233143785764193005 1905364962428919661572377)
                      ·
                        rfl

theorem cell23_3710685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3710685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710685 prefixEnd_3710685 := by exact prefixLift 3710685
  have htrace : WordTrace (prefixWord ++ tailWord_3710685) baseStart_3710685 baseEnd_3710685 := by
    simpa [prefixWord, tailWord_3710685, baseEnd_3710685] using wordTrace_append hprefix tailTrace_3710685
  have hstable : (prefixWord ++ tailWord_3710685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710685).length < 2 ^ (prefixWord ++ tailWord_3710685).sum := by decide
  have hdescent : baseEnd_3710685 < baseStart_3710685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710691 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3710691 : Nat := 118140960795 + 3710691 * 2 ^ 59
def prefixEnd_3710691 : Nat := 4983230072969 + 3 ^ 40 * 3710691 * 2
def baseEnd_3710691 : Nat := 1905368043312846638097349

theorem tailTrace_3710691 : CollatzResearch.WordTrace tailWord_3710691 prefixEnd_3710691 1905368043312846638097349 := by
  unfold tailWord_3710691
  simp only [CollatzResearch.WordTrace]
  refine ⟨135340019399807717413643927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90226679599871811609095951 135340019399807717413643927)
  ·
    refine ⟨203010029099711576120465891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135340019399807717413643927 203010029099711576120465891)
    ·
      refine ⟨304515043649567364180698837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203010029099711576120465891 304515043649567364180698837)
      ·
        refine ⟨7137071335536735097985129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 304515043649567364180698837 7137071335536735097985129)
        ·
          refine ⟨5352803501652551323488847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7137071335536735097985129 5352803501652551323488847)
          ·
            refine ⟨8029205252478826985233271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352803501652551323488847 8029205252478826985233271)
            ·
              refine ⟨12043807878718240477849907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029205252478826985233271 12043807878718240477849907)
              ·
                refine ⟨18065711818077360716774861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12043807878718240477849907 18065711818077360716774861)
                ·
                  refine ⟨6774641931779010268790573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18065711818077360716774861 6774641931779010268790573)
                  ·
                    refine ⟨2540490724417128850796465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6774641931779010268790573 2540490724417128850796465)
                    ·
                      refine ⟨1905368043312846638097349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540490724417128850796465 1905368043312846638097349)
                      ·
                        rfl

theorem cell23_3710691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3710691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710691 prefixEnd_3710691 := by exact prefixLift 3710691
  have htrace : WordTrace (prefixWord ++ tailWord_3710691) baseStart_3710691 baseEnd_3710691 := by
    simpa [prefixWord, tailWord_3710691, baseEnd_3710691] using wordTrace_append hprefix tailTrace_3710691
  have hstable : (prefixWord ++ tailWord_3710691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710691).length < 2 ^ (prefixWord ++ tailWord_3710691).sum := by decide
  have hdescent : baseEnd_3710691 < baseStart_3710691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710704 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 4, 2, 2]
def baseStart_3710704 : Nat := 118140960795 + 3710704 * 2 ^ 59
def prefixEnd_3710704 : Nat := 4983230072969 + 3 ^ 40 * 3710704 * 2
def baseEnd_3710704 : Nat := 1905374718561355087234789

theorem tailTrace_3710704 : CollatzResearch.WordTrace tailWord_3710704 prefixEnd_3710704 1905374718561355087234789 := by
  unfold tailWord_3710704
  simp only [CollatzResearch.WordTrace]
  refine ⟨67670246774380310316933583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90226995699173747089244777 67670246774380310316933583)
  ·
    refine ⟨101505370161570465475400375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67670246774380310316933583 101505370161570465475400375)
    ·
      refine ⟨152258055242355698213100563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101505370161570465475400375 152258055242355698213100563)
      ·
        refine ⟨228387082863533547319650845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152258055242355698213100563 228387082863533547319650845)
        ·
          refine ⟨85645156073825080244869067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228387082863533547319650845 85645156073825080244869067)
          ·
            refine ⟨128467734110737620367303601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85645156073825080244869067 128467734110737620367303601)
            ·
              refine ⟨96350800583053215275477701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128467734110737620367303601 96350800583053215275477701)
              ·
                refine ⟨18065775109322477864152069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96350800583053215275477701 18065775109322477864152069)
                ·
                  refine ⟨3387332832997964599528513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18065775109322477864152069 3387332832997964599528513)
                  ·
                    refine ⟨2540499624748473449646385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387332832997964599528513 2540499624748473449646385)
                    ·
                      refine ⟨1905374718561355087234789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540499624748473449646385 1905374718561355087234789)
                      ·
                        rfl

theorem cell23_3710704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 2, 2].length) (baseStart_3710704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710704 prefixEnd_3710704 := by exact prefixLift 3710704
  have htrace : WordTrace (prefixWord ++ tailWord_3710704) baseStart_3710704 baseEnd_3710704 := by
    simpa [prefixWord, tailWord_3710704, baseEnd_3710704] using wordTrace_append hprefix tailTrace_3710704
  have hstable : (prefixWord ++ tailWord_3710704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710704).length < 2 ^ (prefixWord ++ tailWord_3710704).sum := by decide
  have hdescent : baseEnd_3710704 < baseStart_3710704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710721 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_3710721 : Nat := 118140960795 + 3710721 * 2 ^ 59
def prefixEnd_3710721 : Nat := 4983230072969 + 3 ^ 40 * 3710721 * 2
def baseEnd_3710721 : Nat := 1905383447732481520722211

theorem tailTrace_3710721 : CollatzResearch.WordTrace tailWord_3710721 prefixEnd_3710721 1905383447732481520722211 := by
  unfold tailWord_3710721
  simp only [CollatzResearch.WordTrace]
  refine ⟨135341113589699032537236017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90227409059799355024824011 135341113589699032537236017)
  ·
    refine ⟨101505835192274274402927013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135341113589699032537236017 101505835192274274402927013)
    ·
      refine ⟨19032344098551426450548815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101505835192274274402927013 19032344098551426450548815)
      ·
        refine ⟨28548516147827139675823223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19032344098551426450548815 28548516147827139675823223)
        ·
          refine ⟨42822774221740709513734835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28548516147827139675823223 42822774221740709513734835)
          ·
            refine ⟨64234161332611064270602253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42822774221740709513734835 64234161332611064270602253)
            ·
              refine ⟨24087810499729149101475845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64234161332611064270602253 24087810499729149101475845)
              ·
                refine ⟨4516464468699215456526721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24087810499729149101475845 4516464468699215456526721)
                ·
                  refine ⟨3387348351524411592395041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516464468699215456526721 3387348351524411592395041)
                  ·
                    refine ⟨2540511263643308694296281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387348351524411592395041 2540511263643308694296281)
                    ·
                      refine ⟨1905383447732481520722211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540511263643308694296281 1905383447732481520722211)
                      ·
                        rfl

theorem cell23_3710721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_3710721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710721 prefixEnd_3710721 := by exact prefixLift 3710721
  have htrace : WordTrace (prefixWord ++ tailWord_3710721) baseStart_3710721 baseEnd_3710721 := by
    simpa [prefixWord, tailWord_3710721, baseEnd_3710721] using wordTrace_append hprefix tailTrace_3710721
  have hstable : (prefixWord ++ tailWord_3710721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710721).length < 2 ^ (prefixWord ++ tailWord_3710721).sum := by decide
  have hdescent : baseEnd_3710721 < baseStart_3710721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710738 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3710738 : Nat := 118140960795 + 3710738 * 2 ^ 59
def prefixEnd_3710738 : Nat := 4983230072969 + 3 ^ 40 * 3710738 * 2
def baseEnd_3710738 : Nat := 1905392176903607954209633

theorem tailTrace_3710738 : CollatzResearch.WordTrace tailWord_3710738 prefixEnd_3710738 1905392176903607954209633 := by
  unfold tailWord_3710738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33835433407659361110151217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90227822420424962960403245 33835433407659361110151217)
  ·
    refine ⟨25376575055744520832613413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33835433407659361110151217 25376575055744520832613413)
    ·
      refine ⟨4758107822952097656115015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25376575055744520832613413 4758107822952097656115015)
      ·
        refine ⟨7137161734428146484172523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758107822952097656115015 7137161734428146484172523)
        ·
          refine ⟨10705742601642219726258785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7137161734428146484172523 10705742601642219726258785)
          ·
            refine ⟨8029306951231664794694089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10705742601642219726258785 8029306951231664794694089)
            ·
              refine ⟨6021980213423748596020567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8029306951231664794694089 6021980213423748596020567)
              ·
                refine ⟨9032970320135622894030851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021980213423748596020567 9032970320135622894030851)
                ·
                  refine ⟨13549455480203434341046277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032970320135622894030851 13549455480203434341046277)
                  ·
                    refine ⟨2540522902538143938946177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13549455480203434341046277 2540522902538143938946177)
                    ·
                      refine ⟨1905392176903607954209633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540522902538143938946177 1905392176903607954209633)
                      ·
                        rfl

theorem cell23_3710738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3710738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710738 prefixEnd_3710738 := by exact prefixLift 3710738
  have htrace : WordTrace (prefixWord ++ tailWord_3710738) baseStart_3710738 baseEnd_3710738 := by
    simpa [prefixWord, tailWord_3710738, baseEnd_3710738] using wordTrace_append hprefix tailTrace_3710738
  have hstable : (prefixWord ++ tailWord_3710738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710738).length < 2 ^ (prefixWord ++ tailWord_3710738).sum := by decide
  have hdescent : baseEnd_3710738 < baseStart_3710738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710757 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_3710757 : Nat := 118140960795 + 3710757 * 2 ^ 59
def prefixEnd_3710757 : Nat := 4983230072969 + 3 ^ 40 * 3710757 * 2
def baseEnd_3710757 : Nat := 635133977678681126624015

theorem tailTrace_3710757 : CollatzResearch.WordTrace tailWord_3710757 prefixEnd_3710757 635133977678681126624015 := by
  unfold tailWord_3710757
  simp only [CollatzResearch.WordTrace]
  refine ⟨135342426617568610685546525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90228284411712407123697683 135342426617568610685546525)
  ·
    refine ⟨50753409981588229007079947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135342426617568610685546525 50753409981588229007079947)
    ·
      refine ⟨76130114972382343510619921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50753409981588229007079947 76130114972382343510619921)
      ·
        refine ⟨57097586229286757632964941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76130114972382343510619921 57097586229286757632964941)
        ·
          refine ⟨21411594835982534112361853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57097586229286757632964941 21411594835982534112361853)
          ·
            refine ⟨8029348063493450292135695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21411594835982534112361853 8029348063493450292135695)
            ·
              refine ⟨12044022095240175438203543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029348063493450292135695 12044022095240175438203543)
              ·
                refine ⟨18066033142860263157305315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12044022095240175438203543 18066033142860263157305315)
                ·
                  refine ⟨27099049714290394735957973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18066033142860263157305315 27099049714290394735957973)
                  ·
                    refine ⟨635133977678681126624015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27099049714290394735957973 635133977678681126624015)
                    ·
                      rfl

theorem cell23_3710757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_3710757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710757 prefixEnd_3710757 := by exact prefixLift 3710757
  have htrace : WordTrace (prefixWord ++ tailWord_3710757) baseStart_3710757 baseEnd_3710757 := by
    simpa [prefixWord, tailWord_3710757, baseEnd_3710757] using wordTrace_append hprefix tailTrace_3710757
  have hstable : (prefixWord ++ tailWord_3710757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710757).length < 2 ^ (prefixWord ++ tailWord_3710757).sum := by decide
  have hdescent : baseEnd_3710757 < baseStart_3710757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710794 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_3710794 : Nat := 118140960795 + 3710794 * 2 ^ 59
def prefixEnd_3710794 : Nat := 4983230072969 + 3 ^ 40 * 3710794 * 2
def baseEnd_3710794 : Nat := 1905420931820259735109375

theorem tailTrace_3710794 : CollatzResearch.WordTrace tailWord_3710794 prefixEnd_3710794 1905420931820259735109375 := by
  unfold tailWord_3710794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33835944029608641501160859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90229184078956377336428957 33835944029608641501160859)
  ·
    refine ⟨50753916044412962251741289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33835944029608641501160859 50753916044412962251741289)
    ·
      refine ⟨38065437033309721688805967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50753916044412962251741289 38065437033309721688805967)
      ·
        refine ⟨57098155549964582533208951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38065437033309721688805967 57098155549964582533208951)
        ·
          refine ⟨85647233324946873799813427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57098155549964582533208951 85647233324946873799813427)
          ·
            refine ⟨128470849987420310699720141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85647233324946873799813427 128470849987420310699720141)
            ·
              refine ⟨48176568745282616512395053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128470849987420310699720141 48176568745282616512395053)
              ·
                refine ⟨18066213279480981192148145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48176568745282616512395053 18066213279480981192148145)
                ·
                  refine ⟨13549659959610735894111109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18066213279480981192148145 13549659959610735894111109)
                  ·
                    refine ⟨2540561242427012980145833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13549659959610735894111109 2540561242427012980145833)
                    ·
                      refine ⟨1905420931820259735109375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540561242427012980145833 1905420931820259735109375)
                      ·
                        rfl

theorem cell23_3710794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_3710794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710794 prefixEnd_3710794 := by exact prefixLift 3710794
  have htrace : WordTrace (prefixWord ++ tailWord_3710794) baseStart_3710794 baseEnd_3710794 := by
    simpa [prefixWord, tailWord_3710794, baseEnd_3710794] using wordTrace_append hprefix tailTrace_3710794
  have hstable : (prefixWord ++ tailWord_3710794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710794).length < 2 ^ (prefixWord ++ tailWord_3710794).sum := by decide
  have hdescent : baseEnd_3710794 < baseStart_3710794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710847 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 3, 5]
def baseStart_3710847 : Nat := 118140960795 + 3710847 * 2 ^ 59
def prefixEnd_3710847 : Nat := 4983230072969 + 3 ^ 40 * 3710847 * 2
def baseEnd_3710847 : Nat := 635149382098316009248877

theorem tailTrace_3710847 : CollatzResearch.WordTrace tailWord_3710847 prefixEnd_3710847 635149382098316009248877 := by
  unfold tailWord_3710847
  simp only [CollatzResearch.WordTrace]
  refine ⟨135345709187242556056322795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90230472791495037370881863 135345709187242556056322795)
  ·
    refine ⟨203018563780863834084484193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135345709187242556056322795 203018563780863834084484193)
    ·
      refine ⟨152263922835647875563363145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203018563780863834084484193 152263922835647875563363145)
      ·
        refine ⟨114197942126735906672522359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152263922835647875563363145 114197942126735906672522359)
        ·
          refine ⟨171296913190103860008783539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114197942126735906672522359 171296913190103860008783539)
          ·
            refine ⟨256945369785155790013175309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171296913190103860008783539 256945369785155790013175309)
            ·
              refine ⟨96354513669433421254940741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256945369785155790013175309 96354513669433421254940741)
              ·
                refine ⟨18066471313018766485301389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96354513669433421254940741 18066471313018766485301389)
                ·
                  refine ⟨6774926742382037431988021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18066471313018766485301389 6774926742382037431988021)
                  ·
                    refine ⟨635149382098316009248877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6774926742382037431988021 635149382098316009248877)
                    ·
                      rfl

theorem cell23_3710847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_3710847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710847 prefixEnd_3710847 := by exact prefixLift 3710847
  have htrace : WordTrace (prefixWord ++ tailWord_3710847) baseStart_3710847 baseEnd_3710847 := by
    simpa [prefixWord, tailWord_3710847, baseEnd_3710847] using wordTrace_append hprefix tailTrace_3710847
  have hstable : (prefixWord ++ tailWord_3710847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710847).length < 2 ^ (prefixWord ++ tailWord_3710847).sum := by decide
  have hdescent : baseEnd_3710847 < baseStart_3710847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710851 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 6]
def baseStart_3710851 : Nat := 118140960795 + 3710851 * 2 ^ 59
def prefixEnd_3710851 : Nat := 4983230072969 + 3 ^ 40 * 3710851 * 2
def baseEnd_3710851 : Nat := 211716688913062890232957

theorem tailTrace_3710851 : CollatzResearch.WordTrace tailWord_3710851 prefixEnd_3710851 211716688913062890232957 := by
  unfold tailWord_3710851
  simp only [CollatzResearch.WordTrace]
  refine ⟨135345855079228064739468407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90230570052818709826312271 135345855079228064739468407)
  ·
    refine ⟨203018782618842097109202611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135345855079228064739468407 203018782618842097109202611)
    ·
      refine ⟨304528173928263145663803917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203018782618842097109202611 304528173928263145663803917)
      ·
        refine ⟨114198065223098679623926469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304528173928263145663803917 114198065223098679623926469)
        ·
          refine ⟨21412137229331002429486213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114198065223098679623926469 21412137229331002429486213)
          ·
            refine ⟨4014775730499562955528665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21412137229331002429486213 4014775730499562955528665)
            ·
              refine ⟨3011081797874672216646499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014775730499562955528665 3011081797874672216646499)
              ·
                refine ⟨4516622696812008324969749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011081797874672216646499 4516622696812008324969749)
                ·
                  refine ⟨211716688913062890232957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4516622696812008324969749 211716688913062890232957)
                  ·
                    rfl

theorem cell23_3710851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 6].length) (baseStart_3710851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710851 prefixEnd_3710851 := by exact prefixLift 3710851
  have htrace : WordTrace (prefixWord ++ tailWord_3710851) baseStart_3710851 baseEnd_3710851 := by
    simpa [prefixWord, tailWord_3710851, baseEnd_3710851] using wordTrace_append hprefix tailTrace_3710851
  have hstable : (prefixWord ++ tailWord_3710851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710851).length < 2 ^ (prefixWord ++ tailWord_3710851).sum := by decide
  have hdescent : baseEnd_3710851 < baseStart_3710851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710871 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 2, 3, 2]
def baseStart_3710871 : Nat := 118140960795 + 3710871 * 2 ^ 59
def prefixEnd_3710871 : Nat := 4983230072969 + 3 ^ 40 * 3710871 * 2
def baseEnd_3710871 : Nat := 1905460469830655933846521

theorem tailTrace_3710871 : CollatzResearch.WordTrace tailWord_3710871 prefixEnd_3710871 1905460469830655933846521 := by
  unfold tailWord_3710871
  simp only [CollatzResearch.WordTrace]
  refine ⟨135346584539155608155196467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90231056359437072103464311 135346584539155608155196467)
  ·
    refine ⟨203019876808733412232794701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135346584539155608155196467 203019876808733412232794701)
    ·
      refine ⟨76132453803275029587298013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203019876808733412232794701 76132453803275029587298013)
      ·
        refine ⟨28549670176228136095236755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76132453803275029587298013 28549670176228136095236755)
        ·
          refine ⟨42824505264342204142855133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28549670176228136095236755 42824505264342204142855133)
          ·
            refine ⟨16059189474128326553570675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42824505264342204142855133 16059189474128326553570675)
            ·
              refine ⟨24088784211192489830356013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16059189474128326553570675 24088784211192489830356013)
              ·
                refine ⟨9033294079197183686383505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24088784211192489830356013 9033294079197183686383505)
                ·
                  refine ⟨6774970559397887764787629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033294079197183686383505 6774970559397887764787629)
                  ·
                    refine ⟨2540613959774207911795361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6774970559397887764787629 2540613959774207911795361)
                    ·
                      refine ⟨1905460469830655933846521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540613959774207911795361 1905460469830655933846521)
                      ·
                        rfl

theorem cell23_3710871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_3710871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710871 prefixEnd_3710871 := by exact prefixLift 3710871
  have htrace : WordTrace (prefixWord ++ tailWord_3710871) baseStart_3710871 baseEnd_3710871 := by
    simpa [prefixWord, tailWord_3710871, baseEnd_3710871] using wordTrace_append hprefix tailTrace_3710871
  have hstable : (prefixWord ++ tailWord_3710871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710871).length < 2 ^ (prefixWord ++ tailWord_3710871).sum := by decide
  have hdescent : baseEnd_3710871 < baseStart_3710871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710904 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_3710904 : Nat := 118140960795 + 3710904 * 2 ^ 59
def prefixEnd_3710904 : Nat := 4983230072969 + 3 ^ 40 * 3710904 * 2
def baseEnd_3710904 : Nat := 1905477414692254304733869

theorem tailTrace_3710904 : CollatzResearch.WordTrace tailWord_3710904 prefixEnd_3710904 1905477414692254304733869 := by
  unfold tailWord_3710904
  simp only [CollatzResearch.WordTrace]
  refine ⟨67673894074018027395573883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90231858765357369860765177 67673894074018027395573883)
  ·
    refine ⟨101510841111027041093360825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67673894074018027395573883 101510841111027041093360825)
    ·
      refine ⟨76133130833270280820020619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101510841111027041093360825 76133130833270280820020619)
      ·
        refine ⟨114199696249905421230030929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76133130833270280820020619 114199696249905421230030929)
        ·
          refine ⟨85649772187429065922523197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114199696249905421230030929 85649772187429065922523197)
          ·
            refine ⟨32118664570285899720946199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85649772187429065922523197 32118664570285899720946199)
            ·
              refine ⟨48177996855428849581419299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32118664570285899720946199 48177996855428849581419299)
              ·
                refine ⟨72266995283143274372128949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48177996855428849581419299 72266995283143274372128949)
                ·
                  refine ⟨6775030807794681972387089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72266995283143274372128949 6775030807794681972387089)
                  ·
                    refine ⟨5081273105846011479290317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6775030807794681972387089 5081273105846011479290317)
                    ·
                      refine ⟨1905477414692254304733869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5081273105846011479290317 1905477414692254304733869)
                      ·
                        rfl

theorem cell23_3710904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_3710904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710904 prefixEnd_3710904 := by exact prefixLift 3710904
  have htrace : WordTrace (prefixWord ++ tailWord_3710904) baseStart_3710904 baseEnd_3710904 := by
    simpa [prefixWord, tailWord_3710904, baseEnd_3710904] using wordTrace_append hprefix tailTrace_3710904
  have hstable : (prefixWord ++ tailWord_3710904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710904).length < 2 ^ (prefixWord ++ tailWord_3710904).sum := by decide
  have hdescent : baseEnd_3710904 < baseStart_3710904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710935 : List Nat := [1, 1, 3, 2, 1, 1, 6, 3, 1, 2, 2]
def baseStart_3710935 : Nat := 118140960795 + 3710935 * 2 ^ 59
def prefixEnd_3710935 : Nat := 4983230072969 + 3 ^ 40 * 3710935 * 2
def baseEnd_3710935 : Nat := 1905493332592543683446227

theorem tailTrace_3710935 : CollatzResearch.WordTrace tailWord_3710935 prefixEnd_3710935 1905493332592543683446227 := by
  unfold tailWord_3710935
  simp only [CollatzResearch.WordTrace]
  refine ⟨135348918810923747085526259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90232612540615831390350839 135348918810923747085526259)
  ·
    refine ⟨203023378216385620628289389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135348918810923747085526259 203023378216385620628289389)
    ·
      refine ⟨76133766831144607735608521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203023378216385620628289389 76133766831144607735608521)
      ·
        refine ⟨57100325123358455801706391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76133766831144607735608521 57100325123358455801706391)
        ·
          refine ⟨85650487685037683702559587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57100325123358455801706391 85650487685037683702559587)
          ·
            refine ⟨128475731527556525553839381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85650487685037683702559587 128475731527556525553839381)
            ·
              refine ⟨6022299915354212135336221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128475731527556525553839381 6022299915354212135336221)
              ·
                refine ⟨2258362468257829550751083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6022299915354212135336221 2258362468257829550751083)
                ·
                  refine ⟨3387543702386744326126625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258362468257829550751083 3387543702386744326126625)
                  ·
                    refine ⟨2540657776790058244594969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387543702386744326126625 2540657776790058244594969)
                    ·
                      refine ⟨1905493332592543683446227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540657776790058244594969 1905493332592543683446227)
                      ·
                        rfl

theorem cell23_3710935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_3710935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710935 prefixEnd_3710935 := by exact prefixLift 3710935
  have htrace : WordTrace (prefixWord ++ tailWord_3710935) baseStart_3710935 baseEnd_3710935 := by
    simpa [prefixWord, tailWord_3710935, baseEnd_3710935] using wordTrace_append hprefix tailTrace_3710935
  have hstable : (prefixWord ++ tailWord_3710935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710935).length < 2 ^ (prefixWord ++ tailWord_3710935).sum := by decide
  have hdescent : baseEnd_3710935 < baseStart_3710935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710938 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_3710938 : Nat := 118140960795 + 3710938 * 2 ^ 59
def prefixEnd_3710938 : Nat := 4983230072969 + 3 ^ 40 * 3710938 * 2
def baseEnd_3710938 : Nat := 1905494873034507171708713

theorem tailTrace_3710938 : CollatzResearch.WordTrace tailWord_3710938 prefixEnd_3710938 1905494873034507171708713 := by
  unfold tailWord_3710938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33837257057478219649471367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90232685486608585731923645 33837257057478219649471367)
  ·
    refine ⟨50755885586217329474207051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33837257057478219649471367 50755885586217329474207051)
    ·
      refine ⟨76133828379325994211310577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50755885586217329474207051 76133828379325994211310577)
      ·
        refine ⟨57100371284494495658482933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76133828379325994211310577 57100371284494495658482933)
        ·
          refine ⟨5353159807921358967982775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57100371284494495658482933 5353159807921358967982775)
          ·
            refine ⟨8029739711882038451974163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353159807921358967982775 8029739711882038451974163)
            ·
              refine ⟨12044609567823057677961245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029739711882038451974163 12044609567823057677961245)
              ·
                refine ⟨4516728587933646629235467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12044609567823057677961245 4516728587933646629235467)
                ·
                  refine ⟨6775092881900469943853201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516728587933646629235467 6775092881900469943853201)
                  ·
                    refine ⟨5081319661425352457889901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6775092881900469943853201 5081319661425352457889901)
                    ·
                      refine ⟨1905494873034507171708713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5081319661425352457889901 1905494873034507171708713)
                      ·
                        rfl

theorem cell23_3710938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_3710938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3710938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3710938 prefixEnd_3710938 := by exact prefixLift 3710938
  have htrace : WordTrace (prefixWord ++ tailWord_3710938) baseStart_3710938 baseEnd_3710938 := by
    simpa [prefixWord, tailWord_3710938, baseEnd_3710938] using wordTrace_append hprefix tailTrace_3710938
  have hstable : (prefixWord ++ tailWord_3710938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710938).length < 2 ^ (prefixWord ++ tailWord_3710938).sum := by decide
  have hdescent : baseEnd_3710938 < baseStart_3710938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711025 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 2, 2, 2]
def baseStart_3711025 : Nat := 118140960795 + 3711025 * 2 ^ 59
def prefixEnd_3711025 : Nat := 4983230072969 + 3 ^ 40 * 3711025 * 2
def baseEnd_3711025 : Nat := 1905539545851448331320813

theorem tailTrace_3711025 : CollatzResearch.WordTrace tailWord_3711025 prefixEnd_3711025 1905539545851448331320813 := by
  unfold tailWord_3711025
  simp only [CollatzResearch.WordTrace]
  refine ⟨135352201380597692456302529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90234800920398461637535019 135352201380597692456302529)
  ·
    refine ⟨101514151035448269342226897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135352201380597692456302529 101514151035448269342226897)
    ·
      refine ⟨76135613276586202006670173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101514151035448269342226897 76135613276586202006670173)
      ·
        refine ⟨28550854978719825752501315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76135613276586202006670173 28550854978719825752501315)
        ·
          refine ⟨42826282468079738628751973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28550854978719825752501315 42826282468079738628751973)
          ·
            refine ⟨8029927962764950992890995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42826282468079738628751973 8029927962764950992890995)
            ·
              refine ⟨12044891944147426489336493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029927962764950992890995 12044891944147426489336493)
              ·
                refine ⟨4516834479055284933501185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12044891944147426489336493 4516834479055284933501185)
                ·
                  refine ⟨3387625859291463700125889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516834479055284933501185 3387625859291463700125889)
                  ·
                    refine ⟨2540719394468597775094417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387625859291463700125889 2540719394468597775094417)
                    ·
                      refine ⟨1905539545851448331320813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540719394468597775094417 1905539545851448331320813)
                      ·
                        rfl

theorem cell23_3711025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_3711025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711025 prefixEnd_3711025 := by exact prefixLift 3711025
  have htrace : WordTrace (prefixWord ++ tailWord_3711025) baseStart_3711025 baseEnd_3711025 := by
    simpa [prefixWord, tailWord_3711025, baseEnd_3711025] using wordTrace_append hprefix tailTrace_3711025
  have hstable : (prefixWord ++ tailWord_3711025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711025).length < 2 ^ (prefixWord ++ tailWord_3711025).sum := by decide
  have hdescent : baseEnd_3711025 < baseStart_3711025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711061 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3711061 : Nat := 118140960795 + 3711061 * 2 ^ 59
def prefixEnd_3711061 : Nat := 4983230072969 + 3 ^ 40 * 3711061 * 2
def baseEnd_3711061 : Nat := 635186010385003396823549

theorem tailTrace_3711061 : CollatzResearch.WordTrace tailWord_3711061 prefixEnd_3711061 635186010385003396823549 := by
  unfold tailWord_3711061
  simp only [CollatzResearch.WordTrace]
  refine ⟨135353514408467270604613037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90235676272311513736408691 135353514408467270604613037)
  ·
    refine ⟨50757567903175226476729889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135353514408467270604613037 50757567903175226476729889)
    ·
      refine ⟨38068175927381419857547417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50757567903175226476729889 38068175927381419857547417)
      ·
        refine ⟨28551131945536064893160563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38068175927381419857547417 28551131945536064893160563)
        ·
          refine ⟨42826697918304097339740845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28551131945536064893160563 42826697918304097339740845)
          ·
            refine ⟨16060011719364036502402817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42826697918304097339740845 16060011719364036502402817)
            ·
              refine ⟨12045008789523027376802113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16060011719364036502402817 12045008789523027376802113)
              ·
                refine ⟨9033756592142270532601585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12045008789523027376802113 9033756592142270532601585)
                ·
                  refine ⟨6775317444106702899451189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033756592142270532601585 6775317444106702899451189)
                  ·
                    refine ⟨635186010385003396823549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6775317444106702899451189 635186010385003396823549)
                    ·
                      rfl

theorem cell23_3711061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3711061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711061 prefixEnd_3711061 := by exact prefixLift 3711061
  have htrace : WordTrace (prefixWord ++ tailWord_3711061) baseStart_3711061 baseEnd_3711061 := by
    simpa [prefixWord, tailWord_3711061, baseEnd_3711061] using wordTrace_append hprefix tailTrace_3711061
  have hstable : (prefixWord ++ tailWord_3711061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711061).length < 2 ^ (prefixWord ++ tailWord_3711061).sum := by decide
  have hdescent : baseEnd_3711061 < baseStart_3711061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711068 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_3711068 : Nat := 118140960795 + 3711068 * 2 ^ 59
def prefixEnd_3711068 : Nat := 4983230072969 + 3 ^ 40 * 3711068 * 2
def baseEnd_3711068 : Nat := 1905561625519591663083115

theorem tailTrace_3711068 : CollatzResearch.WordTrace tailWord_3711068 prefixEnd_3711068 1905561625519591663083115 := by
  unfold tailWord_3711068
  simp only [CollatzResearch.WordTrace]
  refine ⟨67676884859720955400058929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90235846479627940533411905 67676884859720955400058929)
  ·
    refine ⟨50757663644790716550044197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67676884859720955400058929 50757663644790716550044197)
    ·
      refine ⟨9517061933398259353133287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50757663644790716550044197 9517061933398259353133287)
      ·
        refine ⟨14275592900097389029699931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9517061933398259353133287 14275592900097389029699931)
        ·
          refine ⟨21413389350146083544549897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14275592900097389029699931 21413389350146083544549897)
          ·
            refine ⟨16060042012609562658412423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21413389350146083544549897 16060042012609562658412423)
            ·
              refine ⟨24090063018914343987618635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060042012609562658412423 24090063018914343987618635)
              ·
                refine ⟨36135094528371515981427953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24090063018914343987618635 36135094528371515981427953)
                ·
                  refine ⟨27101320896278636986070965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36135094528371515981427953 27101320896278636986070965)
                  ·
                    refine ⟨2540748834026122217444153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27101320896278636986070965 2540748834026122217444153)
                    ·
                      refine ⟨1905561625519591663083115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540748834026122217444153 1905561625519591663083115)
                      ·
                        rfl

theorem cell23_3711068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_3711068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711068 prefixEnd_3711068 := by exact prefixLift 3711068
  have htrace : WordTrace (prefixWord ++ tailWord_3711068) baseStart_3711068 baseEnd_3711068 := by
    simpa [prefixWord, tailWord_3711068, baseEnd_3711068] using wordTrace_append hprefix tailTrace_3711068
  have hstable : (prefixWord ++ tailWord_3711068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711068).length < 2 ^ (prefixWord ++ tailWord_3711068).sum := by decide
  have hdescent : baseEnd_3711068 < baseStart_3711068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711104 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 8]
def baseStart_3711104 : Nat := 118140960795 + 3711104 * 2 ^ 59
def prefixEnd_3711104 : Nat := 4983230072969 + 3 ^ 40 * 3711104 * 2
def baseEnd_3711104 : Nat := 211731123424794835803661

theorem tailTrace_3711104 : CollatzResearch.WordTrace tailWord_3711104 prefixEnd_3711104 211731123424794835803661 := by
  unfold tailWord_3711104
  simp only [CollatzResearch.WordTrace]
  refine ⟨67677541373655744474214183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90236721831540992632285577 67677541373655744474214183)
  ·
    refine ⟨101516312060483616711321275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67677541373655744474214183 101516312060483616711321275)
    ·
      refine ⟨152274468090725425066981913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101516312060483616711321275 152274468090725425066981913)
      ·
        refine ⟨114205851068044068800236435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152274468090725425066981913 114205851068044068800236435)
        ·
          refine ⟨171308776602066103200354653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114205851068044068800236435 171308776602066103200354653)
          ·
            refine ⟨64240791225774788700132995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171308776602066103200354653 64240791225774788700132995)
            ·
              refine ⟨96361186838662183050199493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64240791225774788700132995 96361186838662183050199493)
              ·
                refine ⟨18067722532249159321912405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96361186838662183050199493 18067722532249159321912405)
                ·
                  refine ⟨211731123424794835803661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18067722532249159321912405 211731123424794835803661)
                  ·
                    rfl

theorem cell23_3711104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_3711104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711104 prefixEnd_3711104 := by exact prefixLift 3711104
  have htrace : WordTrace (prefixWord ++ tailWord_3711104) baseStart_3711104 baseEnd_3711104 := by
    simpa [prefixWord, tailWord_3711104, baseEnd_3711104] using wordTrace_append hprefix tailTrace_3711104
  have hstable : (prefixWord ++ tailWord_3711104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711104).length < 2 ^ (prefixWord ++ tailWord_3711104).sum := by decide
  have hdescent : baseEnd_3711104 < baseStart_3711104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711168 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 1, 5]
def baseStart_3711168 : Nat := 118140960795 + 3711168 * 2 ^ 59
def prefixEnd_3711168 : Nat := 4983230072969 + 3 ^ 40 * 3711168 * 2
def baseEnd_3711168 : Nat := 635204324528347090610885

theorem tailTrace_3711168 : CollatzResearch.WordTrace tailWord_3711168 prefixEnd_3711168 635204324528347090610885 := by
  unfold tailWord_3711168
  simp only [CollatzResearch.WordTrace]
  refine ⟨67678708509539813939379079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90238278012719751919172105 67678708509539813939379079)
  ·
    refine ⟨101518062764309720909068619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67678708509539813939379079 101518062764309720909068619)
    ·
      refine ⟨152277094146464581363602929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101518062764309720909068619 152277094146464581363602929)
      ·
        refine ⟨114207820609848436022702197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152277094146464581363602929 114207820609848436022702197)
        ·
          refine ⟨10706983182173290877128331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114207820609848436022702197 10706983182173290877128331)
          ·
            refine ⟨16060474773259936315692497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10706983182173290877128331 16060474773259936315692497)
            ·
              refine ⟨12045356079944952236769373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16060474773259936315692497 12045356079944952236769373)
              ·
                refine ⟨4517008529979357088788515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12045356079944952236769373 4517008529979357088788515)
                ·
                  refine ⟨6775512794969035633182773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517008529979357088788515 6775512794969035633182773)
                  ·
                    refine ⟨635204324528347090610885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6775512794969035633182773 635204324528347090610885)
                    ·
                      rfl

theorem cell23_3711168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_3711168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711168 prefixEnd_3711168 := by exact prefixLift 3711168
  have htrace : WordTrace (prefixWord ++ tailWord_3711168) baseStart_3711168 baseEnd_3711168 := by
    simpa [prefixWord, tailWord_3711168, baseEnd_3711168] using wordTrace_append hprefix tailTrace_3711168
  have hstable : (prefixWord ++ tailWord_3711168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711168).length < 2 ^ (prefixWord ++ tailWord_3711168).sum := by decide
  have hdescent : baseEnd_3711168 < baseStart_3711168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711182 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3711182 : Nat := 118140960795 + 3711182 * 2 ^ 59
def prefixEnd_3711182 : Nat := 4983230072969 + 3 ^ 40 * 3711182 * 2
def baseEnd_3711182 : Nat := 1905620162314204217057591

theorem tailTrace_3711182 : CollatzResearch.WordTrace tailWord_3711182 prefixEnd_3711182 1905620162314204217057591 := by
  unfold tailWord_3711182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919740955128613533720975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90238618427352605513178533 16919740955128613533720975)
  ·
    refine ⟨25379611432692920300581463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16919740955128613533720975 25379611432692920300581463)
    ·
      refine ⟨38069417149039380450872195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25379611432692920300581463 38069417149039380450872195)
      ·
        refine ⟨57104125723559070676308293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38069417149039380450872195 57104125723559070676308293)
        ·
          refine ⟨10707023573167325751807805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57104125723559070676308293 10707023573167325751807805)
          ·
            refine ⟨4015133839937747156927927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10707023573167325751807805 4015133839937747156927927)
            ·
              refine ⟨6022700759906620735391891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015133839937747156927927 6022700759906620735391891)
              ·
                refine ⟨9034051139859931103087837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6022700759906620735391891 9034051139859931103087837)
                ·
                  refine ⟨3387769177447474163657939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9034051139859931103087837 3387769177447474163657939)
                  ·
                    refine ⟨5081653766171211245486909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3387769177447474163657939 5081653766171211245486909)
                    ·
                      refine ⟨1905620162314204217057591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5081653766171211245486909 1905620162314204217057591)
                      ·
                        rfl

theorem cell23_3711182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3711182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711182 prefixEnd_3711182 := by exact prefixLift 3711182
  have htrace : WordTrace (prefixWord ++ tailWord_3711182) baseStart_3711182 baseEnd_3711182 := by
    simpa [prefixWord, tailWord_3711182, baseEnd_3711182] using wordTrace_append hprefix tailTrace_3711182
  have hstable : (prefixWord ++ tailWord_3711182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711182).length < 2 ^ (prefixWord ++ tailWord_3711182).sum := by decide
  have hdescent : baseEnd_3711182 < baseStart_3711182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711191 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_3711191 : Nat := 118140960795 + 3711191 * 2 ^ 59
def prefixEnd_3711191 : Nat := 4983230072969 + 3 ^ 40 * 3711191 * 2
def baseEnd_3711191 : Nat := 1905624783640094681845049

theorem tailTrace_3711191 : CollatzResearch.WordTrace tailWord_3711191 prefixEnd_3711191 1905624783640094681845049 := by
  unfold tailWord_3711191
  simp only [CollatzResearch.WordTrace]
  refine ⟨135358255897996302806845427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90238837265330868537896951 135358255897996302806845427)
  ·
    refine ⟨203037383846994454210268141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135358255897996302806845427 203037383846994454210268141)
    ·
      refine ⟨76139018942622920328850553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203037383846994454210268141 76139018942622920328850553)
      ·
        refine ⟨57104264206967190246637915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76139018942622920328850553 57104264206967190246637915)
        ·
          refine ⟨85656396310450785369956873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57104264206967190246637915 85656396310450785369956873)
          ·
            refine ⟨64242297232838089027467655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85656396310450785369956873 64242297232838089027467655)
            ·
              refine ⟨96363445849257133541201483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64242297232838089027467655 96363445849257133541201483)
              ·
                refine ⟨144545168773885700311802225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96363445849257133541201483 144545168773885700311802225)
                ·
                  refine ⟨108408876580414275233851669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144545168773885700311802225 108408876580414275233851669)
                  ·
                    refine ⟨5081666089706919151586797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108408876580414275233851669 5081666089706919151586797)
                    ·
                      refine ⟨1905624783640094681845049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5081666089706919151586797 1905624783640094681845049)
                      ·
                        rfl

theorem cell23_3711191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_3711191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711191 prefixEnd_3711191 := by exact prefixLift 3711191
  have htrace : WordTrace (prefixWord ++ tailWord_3711191) baseStart_3711191 baseEnd_3711191 := by
    simpa [prefixWord, tailWord_3711191, baseEnd_3711191] using wordTrace_append hprefix tailTrace_3711191
  have hstable : (prefixWord ++ tailWord_3711191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711191).length < 2 ^ (prefixWord ++ tailWord_3711191).sum := by decide
  have hdescent : baseEnd_3711191 < baseStart_3711191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711201 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3711201 : Nat := 118140960795 + 3711201 * 2 ^ 59
def prefixEnd_3711201 : Nat := 4983230072969 + 3 ^ 40 * 3711201 * 2
def baseEnd_3711201 : Nat := 1905629918446639642720003

theorem tailTrace_3711201 : CollatzResearch.WordTrace tailWord_3711201 prefixEnd_3711201 1905629918446639642720003 := by
  unfold tailWord_3711201
  simp only [CollatzResearch.WordTrace]
  refine ⟨135358620627960074514709457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90239080418640049676472971 135358620627960074514709457)
  ·
    refine ⟨101518965470970055886032093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135358620627960074514709457 101518965470970055886032093)
    ·
      refine ⟨38069612051613770957262035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101518965470970055886032093 38069612051613770957262035)
      ·
        refine ⟨57104418077420656435893053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38069612051613770957262035 57104418077420656435893053)
        ·
          refine ⟨21414156779032746163459895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57104418077420656435893053 21414156779032746163459895)
          ·
            refine ⟨32121235168549119245189843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21414156779032746163459895 32121235168549119245189843)
            ·
              refine ⟨48181852752823678867784765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32121235168549119245189843 48181852752823678867784765)
              ·
                refine ⟨18068194782308879575419287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48181852752823678867784765 18068194782308879575419287)
                ·
                  refine ⟨27102292173463319363128931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18068194782308879575419287 27102292173463319363128931)
                  ·
                    refine ⟨40653438260194979044693397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27102292173463319363128931 40653438260194979044693397)
                    ·
                      refine ⟨1905629918446639642720003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40653438260194979044693397 1905629918446639642720003)
                      ·
                        rfl

theorem cell23_3711201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3711201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711201 prefixEnd_3711201 := by exact prefixLift 3711201
  have htrace : WordTrace (prefixWord ++ tailWord_3711201) baseStart_3711201 baseEnd_3711201 := by
    simpa [prefixWord, tailWord_3711201, baseEnd_3711201] using wordTrace_append hprefix tailTrace_3711201
  have hstable : (prefixWord ++ tailWord_3711201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711201).length < 2 ^ (prefixWord ++ tailWord_3711201).sum := by decide
  have hdescent : baseEnd_3711201 < baseStart_3711201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711205 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3711205 : Nat := 118140960795 + 3711205 * 2 ^ 59
def prefixEnd_3711205 : Nat := 4983230072969 + 3 ^ 40 * 3711205 * 2
def baseEnd_3711205 : Nat := 1905631972369257627069985

theorem tailTrace_3711205 : CollatzResearch.WordTrace tailWord_3711205 prefixEnd_3711205 1905631972369257627069985 := by
  unfold tailWord_3711205
  simp only [CollatzResearch.WordTrace]
  refine ⟨135358766519945583197855069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90239177679963722131903379 135358766519945583197855069)
  ·
    refine ⟨50759537444979593699195651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135358766519945583197855069 50759537444979593699195651)
    ·
      refine ⟨76139306167469390548793477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50759537444979593699195651 76139306167469390548793477)
      ·
        refine ⟨14276119906400510727898777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76139306167469390548793477 14276119906400510727898777)
        ·
          refine ⟨10707089929800383045924083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14276119906400510727898777 10707089929800383045924083)
          ·
            refine ⟨16060634894700574568886125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10707089929800383045924083 16060634894700574568886125)
            ·
              refine ⟨6022738085512715463332297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16060634894700574568886125 6022738085512715463332297)
              ·
                refine ⟨4517053564134536597499223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6022738085512715463332297 4517053564134536597499223)
                ·
                  refine ⟨6775580346201804896248835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517053564134536597499223 6775580346201804896248835)
                  ·
                    refine ⟨10163370519302707344373253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6775580346201804896248835 10163370519302707344373253)
                    ·
                      refine ⟨1905631972369257627069985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10163370519302707344373253 1905631972369257627069985)
                      ·
                        rfl

theorem cell23_3711205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3711205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711205 prefixEnd_3711205 := by exact prefixLift 3711205
  have htrace : WordTrace (prefixWord ++ tailWord_3711205) baseStart_3711205 baseEnd_3711205 := by
    simpa [prefixWord, tailWord_3711205, baseEnd_3711205] using wordTrace_append hprefix tailTrace_3711205
  have hstable : (prefixWord ++ tailWord_3711205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711205).length < 2 ^ (prefixWord ++ tailWord_3711205).sum := by decide
  have hdescent : baseEnd_3711205 < baseStart_3711205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711218 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3711218 : Nat := 118140960795 + 3711218 * 2 ^ 59
def prefixEnd_3711218 : Nat := 4983230072969 + 3 ^ 40 * 3711218 * 2
def baseEnd_3711218 : Nat := 1905638647617766076207425

theorem tailTrace_3711218 : CollatzResearch.WordTrace tailWord_3711218 prefixEnd_3711218 1905638647617766076207425 := by
  unfold tailWord_3711218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33839810167224621604519577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90239493779265657612052205 33839810167224621604519577)
  ·
    refine ⟨25379857625418466203389683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33839810167224621604519577 25379857625418466203389683)
    ·
      refine ⟨38069786438127699305084525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25379857625418466203389683 38069786438127699305084525)
      ·
        refine ⟨14276169914297887239406697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38069786438127699305084525 14276169914297887239406697)
        ·
          refine ⟨10707127435723415429555023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14276169914297887239406697 10707127435723415429555023)
          ·
            refine ⟨16060691153585123144332535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10707127435723415429555023 16060691153585123144332535)
            ·
              refine ⟨24091036730377684716498803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060691153585123144332535 24091036730377684716498803)
              ·
                refine ⟨36136555095566527074748205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24091036730377684716498803 36136555095566527074748205)
                ·
                  refine ⟨13551208160837447653030577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36136555095566527074748205 13551208160837447653030577)
                  ·
                    refine ⟨10163406120628085739772933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13551208160837447653030577 10163406120628085739772933)
                    ·
                      refine ⟨1905638647617766076207425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10163406120628085739772933 1905638647617766076207425)
                      ·
                        rfl

theorem cell23_3711218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3711218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711218 prefixEnd_3711218 := by exact prefixLift 3711218
  have htrace : WordTrace (prefixWord ++ tailWord_3711218) baseStart_3711218 baseEnd_3711218 := by
    simpa [prefixWord, tailWord_3711218, baseEnd_3711218] using wordTrace_append hprefix tailTrace_3711218
  have hstable : (prefixWord ++ tailWord_3711218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711218).length < 2 ^ (prefixWord ++ tailWord_3711218).sum := by decide
  have hdescent : baseEnd_3711218 < baseStart_3711218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711241 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 2, 7]
def baseStart_3711241 : Nat := 118140960795 + 3711241 * 2 ^ 59
def prefixEnd_3711241 : Nat := 4983230072969 + 3 ^ 40 * 3711241 * 2
def baseEnd_3711241 : Nat := 635216819224273162073273

theorem tailTrace_3711241 : CollatzResearch.WordTrace tailWord_3711241 prefixEnd_3711241 635216819224273162073273 := by
  unfold tailWord_3711241
  simp only [CollatzResearch.WordTrace]
  refine ⟨135360079547815161346165577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90240053031876774230777051 135360079547815161346165577)
  ·
    refine ⟨101520059660861371009624183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135360079547815161346165577 101520059660861371009624183)
    ·
      refine ⟨152280089491292056514436275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101520059660861371009624183 152280089491292056514436275)
      ·
        refine ⟨228420134236938084771654413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152280089491292056514436275 228420134236938084771654413)
        ·
          refine ⟨85657550338851781789370405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228420134236938084771654413 85657550338851781789370405)
          ·
            refine ⟨16060790688534709085506951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85657550338851781789370405 16060790688534709085506951)
            ·
              refine ⟨24091186032802063628260427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060790688534709085506951 24091186032802063628260427)
              ·
                refine ⟨36136779049203095442390641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24091186032802063628260427 36136779049203095442390641)
                ·
                  refine ⟨27102584286902321581792981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36136779049203095442390641 27102584286902321581792981)
                  ·
                    refine ⟨635216819224273162073273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27102584286902321581792981 635216819224273162073273)
                    ·
                      rfl

theorem cell23_3711241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_3711241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711241 prefixEnd_3711241 := by exact prefixLift 3711241
  have htrace : WordTrace (prefixWord ++ tailWord_3711241) baseStart_3711241 baseEnd_3711241 := by
    simpa [prefixWord, tailWord_3711241, baseEnd_3711241] using wordTrace_append hprefix tailTrace_3711241
  have hstable : (prefixWord ++ tailWord_3711241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711241).length < 2 ^ (prefixWord ++ tailWord_3711241).sum := by decide
  have hdescent : baseEnd_3711241 < baseStart_3711241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711255 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3711255 : Nat := 118140960795 + 3711255 * 2 ^ 59
def prefixEnd_3711255 : Nat := 4983230072969 + 3 ^ 40 * 3711255 * 2
def baseEnd_3711255 : Nat := 1905657646401982431444755

theorem tailTrace_3711255 : CollatzResearch.WordTrace tailWord_3711255 prefixEnd_3711255 1905657646401982431444755 := by
  unfold tailWord_3711255
  simp only [CollatzResearch.WordTrace]
  refine ⟨135360590169764441737175219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90240393446509627824783479 135360590169764441737175219)
  ·
    refine ⟨203040885254646662605762829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135360590169764441737175219 203040885254646662605762829)
    ·
      refine ⟨76140331970492498477161061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203040885254646662605762829 76140331970492498477161061)
      ·
        refine ⟨14276312244467343464467699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76140331970492498477161061 14276312244467343464467699)
        ·
          refine ⟨21414468366701015196701549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14276312244467343464467699 21414468366701015196701549)
          ·
            refine ⟨8030425637512880698763081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21414468366701015196701549 8030425637512880698763081)
            ·
              refine ⟨6022819228134660524072311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8030425637512880698763081 6022819228134660524072311)
              ·
                refine ⟨9034228842201990786108467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6022819228134660524072311 9034228842201990786108467)
                ·
                  refine ⟨13551343263302986179162701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9034228842201990786108467 13551343263302986179162701)
                  ·
                    refine ⟨5081753723738619817186013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13551343263302986179162701 5081753723738619817186013)
                    ·
                      refine ⟨1905657646401982431444755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5081753723738619817186013 1905657646401982431444755)
                      ·
                        rfl

theorem cell23_3711255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3711255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711255 prefixEnd_3711255 := by exact prefixLift 3711255
  have htrace : WordTrace (prefixWord ++ tailWord_3711255) baseStart_3711255 baseEnd_3711255 := by
    simpa [prefixWord, tailWord_3711255, baseEnd_3711255] using wordTrace_append hprefix tailTrace_3711255
  have hstable : (prefixWord ++ tailWord_3711255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711255).length < 2 ^ (prefixWord ++ tailWord_3711255).sum := by decide
  have hdescent : baseEnd_3711255 < baseStart_3711255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711262 : List Nat := [4, 3, 2, 1, 1, 2, 3, 7]
def baseStart_3711262 : Nat := 118140960795 + 3711262 * 2 ^ 59
def prefixEnd_3711262 : Nat := 4983230072969 + 3 ^ 40 * 3711262 * 2
def baseEnd_3711262 : Nat := 70580045954317181631749

theorem tailTrace_3711262 : CollatzResearch.WordTrace tailWord_3711262 prefixEnd_3711262 70580045954317181631749 := by
  unfold tailWord_3711262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16920105685092385241585005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90240563653826054621786693 16920105685092385241585005)
  ·
    refine ⟨6345039631909644465594377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16920105685092385241585005 6345039631909644465594377)
    ·
      refine ⟨4758779723932233349195783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6345039631909644465594377 4758779723932233349195783)
      ·
        refine ⟨7138169585898350023793675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758779723932233349195783 7138169585898350023793675)
        ·
          refine ⟨10707254378847525035690513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138169585898350023793675 10707254378847525035690513)
          ·
            refine ⟨8030440784135643776767885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10707254378847525035690513 8030440784135643776767885)
            ·
              refine ⟨3011415294050866416287957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8030440784135643776767885 3011415294050866416287957)
              ·
                refine ⟨70580045954317181631749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3011415294050866416287957 70580045954317181631749)
                ·
                  rfl

theorem cell23_3711262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_3711262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711262 prefixEnd_3711262 := by exact prefixLift 3711262
  have htrace : WordTrace (prefixWord ++ tailWord_3711262) baseStart_3711262 baseEnd_3711262 := by
    simpa [prefixWord, tailWord_3711262, baseEnd_3711262] using wordTrace_append hprefix tailTrace_3711262
  have hstable : (prefixWord ++ tailWord_3711262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711262).length < 2 ^ (prefixWord ++ tailWord_3711262).sum := by decide
  have hdescent : baseEnd_3711262 < baseStart_3711262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711265 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3711265 : Nat := 118140960795 + 3711265 * 2 ^ 59
def prefixEnd_3711265 : Nat := 4983230072969 + 3 ^ 40 * 3711265 * 2
def baseEnd_3711265 : Nat := 1905662781208527392319709

theorem tailTrace_3711265 : CollatzResearch.WordTrace tailWord_3711265 prefixEnd_3711265 1905662781208527392319709 := by
  unfold tailWord_3711265
  simp only [CollatzResearch.WordTrace]
  refine ⟨135360954899728213445039249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90240636599818808963359499 135360954899728213445039249)
  ·
    refine ⟨101520716174796160083779437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135360954899728213445039249 101520716174796160083779437)
    ·
      refine ⟨38070268565548560031417289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101520716174796160083779437 38070268565548560031417289)
      ·
        refine ⟨28552701424161420023562967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38070268565548560031417289 28552701424161420023562967)
        ·
          refine ⟨42829052136242130035344451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28552701424161420023562967 42829052136242130035344451)
          ·
            refine ⟨64243578204363195053016677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42829052136242130035344451 64243578204363195053016677)
            ·
              refine ⟨12045670913318099072440627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64243578204363195053016677 12045670913318099072440627)
              ·
                refine ⟨18068506369977148608660941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12045670913318099072440627 18068506369977148608660941)
                ·
                  refine ⟨6775689888741430728247853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18068506369977148608660941 6775689888741430728247853)
                  ·
                    refine ⟨2540883708278036523092945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6775689888741430728247853 2540883708278036523092945)
                    ·
                      refine ⟨1905662781208527392319709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540883708278036523092945 1905662781208527392319709)
                      ·
                        rfl

theorem cell23_3711265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3711265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711265 prefixEnd_3711265 := by exact prefixLift 3711265
  have htrace : WordTrace (prefixWord ++ tailWord_3711265) baseStart_3711265 baseEnd_3711265 := by
    simpa [prefixWord, tailWord_3711265, baseEnd_3711265] using wordTrace_append hprefix tailTrace_3711265
  have hstable : (prefixWord ++ tailWord_3711265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711265).length < 2 ^ (prefixWord ++ tailWord_3711265).sum := by decide
  have hdescent : baseEnd_3711265 < baseStart_3711265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711289 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3711289 : Nat := 118140960795 + 3711289 * 2 ^ 59
def prefixEnd_3711289 : Nat := 4983230072969 + 3 ^ 40 * 3711289 * 2
def baseEnd_3711289 : Nat := 1905675104744235298419599

theorem tailTrace_3711289 : CollatzResearch.WordTrace tailWord_3711289 prefixEnd_3711289 1905675104744235298419599 := by
  unfold tailWord_3711289
  simp only [CollatzResearch.WordTrace]
  refine ⟨135361830251641265543912921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90241220167760843695941947 135361830251641265543912921)
  ·
    refine ⟨101521372688730949157934691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135361830251641265543912921 101521372688730949157934691)
    ·
      refine ⟨152282059033096423736902037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101521372688730949157934691 152282059033096423736902037)
      ·
        refine ⟨7138221517176394862667283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152282059033096423736902037 7138221517176394862667283)
        ·
          refine ⟨10707332275764592294000925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138221517176394862667283 10707332275764592294000925)
          ·
            refine ⟨4015249603411722110250347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10707332275764592294000925 4015249603411722110250347)
            ·
              refine ⟨6022874405117583165375521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015249603411722110250347 6022874405117583165375521)
              ·
                refine ⟨4517155803838187374031641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6022874405117583165375521 4517155803838187374031641)
                ·
                  refine ⟨3387866852878640530523731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4517155803838187374031641 3387866852878640530523731)
                  ·
                    refine ⟨5081800279317960795785597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3387866852878640530523731 5081800279317960795785597)
                    ·
                      refine ⟨1905675104744235298419599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5081800279317960795785597 1905675104744235298419599)
                      ·
                        rfl

theorem cell23_3711289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3711289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711289 prefixEnd_3711289 := by exact prefixLift 3711289
  have htrace : WordTrace (prefixWord ++ tailWord_3711289) baseStart_3711289 baseEnd_3711289 := by
    simpa [prefixWord, tailWord_3711289, baseEnd_3711289] using wordTrace_append hprefix tailTrace_3711289
  have hstable : (prefixWord ++ tailWord_3711289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711289).length < 2 ^ (prefixWord ++ tailWord_3711289).sum := by decide
  have hdescent : baseEnd_3711289 < baseStart_3711289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711291 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4]
def baseStart_3711291 : Nat := 118140960795 + 3711291 * 2 ^ 59
def prefixEnd_3711291 : Nat := 4983230072969 + 3 ^ 40 * 3711291 * 2
def baseEnd_3711291 : Nat := 1905676131705544290594589

theorem tailTrace_3711291 : CollatzResearch.WordTrace tailWord_3711291 prefixEnd_3711291 1905676131705544290594589 := by
  unfold tailWord_3711291
  simp only [CollatzResearch.WordTrace]
  refine ⟨135361903197634019885485727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90241268798422679923657151 135361903197634019885485727)
  ·
    refine ⟨203042854796451029828228591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135361903197634019885485727 203042854796451029828228591)
    ·
      refine ⟨304564282194676544742342887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203042854796451029828228591 304564282194676544742342887)
      ·
        refine ⟨456846423292014817113514331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304564282194676544742342887 456846423292014817113514331)
        ·
          refine ⟨685269634938022225670271497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456846423292014817113514331 685269634938022225670271497)
          ·
            refine ⟨513952226203516669252703623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685269634938022225670271497 513952226203516669252703623)
            ·
              refine ⟨770928339305275003879055435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513952226203516669252703623 770928339305275003879055435)
              ·
                refine ⟨1156392508957912505818583153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770928339305275003879055435 1156392508957912505818583153)
                ·
                  refine ⟨867294381718434379363937365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1156392508957912505818583153 867294381718434379363937365)
                  ·
                    refine ⟨10163606035762902883171141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 867294381718434379363937365 10163606035762902883171141)
                    ·
                      refine ⟨1905676131705544290594589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10163606035762902883171141 1905676131705544290594589)
                      ·
                        rfl

theorem cell23_3711291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_3711291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711291 prefixEnd_3711291 := by exact prefixLift 3711291
  have htrace : WordTrace (prefixWord ++ tailWord_3711291) baseStart_3711291 baseEnd_3711291 := by
    simpa [prefixWord, tailWord_3711291, baseEnd_3711291] using wordTrace_append hprefix tailTrace_3711291
  have hstable : (prefixWord ++ tailWord_3711291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711291).length < 2 ^ (prefixWord ++ tailWord_3711291).sum := by decide
  have hdescent : baseEnd_3711291 < baseStart_3711291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711308 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3711308 : Nat := 118140960795 + 3711308 * 2 ^ 59
def prefixEnd_3711308 : Nat := 4983230072969 + 3 ^ 40 * 3711308 * 2
def baseEnd_3711308 : Nat := 1905684860876670724082011

theorem tailTrace_3711308 : CollatzResearch.WordTrace tailWord_3711308 prefixEnd_3711308 1905684860876670724082011 := by
  unfold tailWord_3711308
  simp only [CollatzResearch.WordTrace]
  refine ⟨67681261619286215894427289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90241682159048287859236385 67681261619286215894427289)
  ·
    refine ⟨50760946214464661920820467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67681261619286215894427289 50760946214464661920820467)
    ·
      refine ⟨76141419321696992881230701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50760946214464661920820467 76141419321696992881230701)
      ·
        refine ⟨28553032245636372330461513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76141419321696992881230701 28553032245636372330461513)
        ·
          refine ⟨21414774184227279247846135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28553032245636372330461513 21414774184227279247846135)
          ·
            refine ⟨32122161276340918871769203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21414774184227279247846135 32122161276340918871769203)
            ·
              refine ⟨48183241914511378307653805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32122161276340918871769203 48183241914511378307653805)
              ·
                refine ⟨18068715717941766865370177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48183241914511378307653805 18068715717941766865370177)
                ·
                  refine ⟨13551536788456325149027633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18068715717941766865370177 13551536788456325149027633)
                  ·
                    refine ⟨10163652591342243861770725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13551536788456325149027633 10163652591342243861770725)
                    ·
                      refine ⟨1905684860876670724082011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10163652591342243861770725 1905684860876670724082011)
                      ·
                        rfl

theorem cell23_3711308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3711308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711308 prefixEnd_3711308 := by exact prefixLift 3711308
  have htrace : WordTrace (prefixWord ++ tailWord_3711308) baseStart_3711308 baseEnd_3711308 := by
    simpa [prefixWord, tailWord_3711308, baseEnd_3711308] using wordTrace_append hprefix tailTrace_3711308
  have hstable : (prefixWord ++ tailWord_3711308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711308).length < 2 ^ (prefixWord ++ tailWord_3711308).sum := by decide
  have hdescent : baseEnd_3711308 < baseStart_3711308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711312 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 1, 4, 2]
def baseStart_3711312 : Nat := 118140960795 + 3711312 * 2 ^ 59
def prefixEnd_3711312 : Nat := 4983230072969 + 3 ^ 40 * 3711312 * 2
def baseEnd_3711312 : Nat := 1905686914799288708431993

theorem tailTrace_3711312 : CollatzResearch.WordTrace tailWord_3711312 prefixEnd_3711312 1905686914799288708431993 := by
  unfold tailWord_3711312
  simp only [CollatzResearch.WordTrace]
  refine ⟨67681334565278970236000095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90241779420371960314666793 67681334565278970236000095)
  ·
    refine ⟨101522001847918455354000143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67681334565278970236000095 101522001847918455354000143)
    ·
      refine ⟨152283002771877683031000215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101522001847918455354000143 152283002771877683031000215)
      ·
        refine ⟨228424504157816524546500323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152283002771877683031000215 228424504157816524546500323)
        ·
          refine ⟨342636756236724786819750485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228424504157816524546500323 342636756236724786819750485)
          ·
            refine ⟨4015274487149118595543951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 342636756236724786819750485 4015274487149118595543951)
            ·
              refine ⟨6022911730723677893315927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015274487149118595543951 6022911730723677893315927)
              ·
                refine ⟨9034367596085516839973891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6022911730723677893315927 9034367596085516839973891)
                ·
                  refine ⟨13551551394128275259960837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9034367596085516839973891 13551551394128275259960837)
                  ·
                    refine ⟨2540915886399051611242657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13551551394128275259960837 2540915886399051611242657)
                    ·
                      refine ⟨1905686914799288708431993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540915886399051611242657 1905686914799288708431993)
                      ·
                        rfl

theorem cell23_3711312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 4, 2].length) (baseStart_3711312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711312 prefixEnd_3711312 := by exact prefixLift 3711312
  have htrace : WordTrace (prefixWord ++ tailWord_3711312) baseStart_3711312 baseEnd_3711312 := by
    simpa [prefixWord, tailWord_3711312, baseEnd_3711312] using wordTrace_append hprefix tailTrace_3711312
  have hstable : (prefixWord ++ tailWord_3711312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711312).length < 2 ^ (prefixWord ++ tailWord_3711312).sum := by decide
  have hdescent : baseEnd_3711312 < baseStart_3711312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711363 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 2, 2, 2]
def baseStart_3711363 : Nat := 118140960795 + 3711363 * 2 ^ 59
def prefixEnd_3711363 : Nat := 4983230072969 + 3 ^ 40 * 3711363 * 2
def baseEnd_3711363 : Nat := 1905713102312668008894259

theorem tailTrace_3711363 : CollatzResearch.WordTrace tailWord_3711363 prefixEnd_3711363 1905713102312668008894259 := by
  unfold tailWord_3711363
  simp only [CollatzResearch.WordTrace]
  refine ⟨135364529253373176182106743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90243019502248784121404495 135364529253373176182106743)
  ·
    refine ⟨203046793880059764273160115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135364529253373176182106743 203046793880059764273160115)
    ·
      refine ⟨304570190820089646409740173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203046793880059764273160115 304570190820089646409740173)
      ·
        refine ⟨114213821557533617403652565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304570190820089646409740173 114213821557533617403652565)
        ·
          refine ⟨2676886442754694157898107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 114213821557533617403652565 2676886442754694157898107)
          ·
            refine ⟨4015329664132041236847161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676886442754694157898107 4015329664132041236847161)
            ·
              refine ⟨3011497248099030927635371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015329664132041236847161 3011497248099030927635371)
              ·
                refine ⟨4517245872148546391453057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011497248099030927635371 4517245872148546391453057)
                ·
                  refine ⟨3387934404111409793589793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4517245872148546391453057 3387934404111409793589793)
                  ·
                    refine ⟨2540950803083557345192345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387934404111409793589793 2540950803083557345192345)
                    ·
                      refine ⟨1905713102312668008894259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2540950803083557345192345 1905713102312668008894259)
                      ·
                        rfl

theorem cell23_3711363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_3711363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711363 prefixEnd_3711363 := by exact prefixLift 3711363
  have htrace : WordTrace (prefixWord ++ tailWord_3711363) baseStart_3711363 baseEnd_3711363 := by
    simpa [prefixWord, tailWord_3711363, baseEnd_3711363] using wordTrace_append hprefix tailTrace_3711363
  have hstable : (prefixWord ++ tailWord_3711363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711363).length < 2 ^ (prefixWord ++ tailWord_3711363).sum := by decide
  have hdescent : baseEnd_3711363 < baseStart_3711363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711385 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 4]
def baseStart_3711385 : Nat := 118140960795 + 3711385 * 2 ^ 59
def prefixEnd_3711385 : Nat := 4983230072969 + 3 ^ 40 * 3711385 * 2
def baseEnd_3711385 : Nat := 1905724398887066922819157

theorem tailTrace_3711385 : CollatzResearch.WordTrace tailWord_3711385 prefixEnd_3711385 1905724398887066922819157 := by
  unfold tailWord_3711385
  simp only [CollatzResearch.WordTrace]
  refine ⟨135365331659293473939407609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90243554439528982626271739 135365331659293473939407609)
  ·
    refine ⟨101523998744470105454555707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135365331659293473939407609 101523998744470105454555707)
    ·
      refine ⟨152285998116705158181833561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101523998744470105454555707 152285998116705158181833561)
      ·
        refine ⟨114214498587528868636375171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152285998116705158181833561 114214498587528868636375171)
        ·
          refine ⟨171321747881293302954562757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114214498587528868636375171 171321747881293302954562757)
          ·
            refine ⟨32122827727742494303980517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171321747881293302954562757 32122827727742494303980517)
            ·
              refine ⟨6023030198951717681996347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32122827727742494303980517 6023030198951717681996347)
              ·
                refine ⟨9034545298427576522994521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023030198951717681996347 9034545298427576522994521)
                ·
                  refine ⟨6775908973820682392245891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9034545298427576522994521 6775908973820682392245891)
                  ·
                    refine ⟨10163863460731023588368837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6775908973820682392245891 10163863460731023588368837)
                    ·
                      refine ⟨1905724398887066922819157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10163863460731023588368837 1905724398887066922819157)
                      ·
                        rfl

theorem cell23_3711385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_3711385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711385 prefixEnd_3711385 := by exact prefixLift 3711385
  have htrace : WordTrace (prefixWord ++ tailWord_3711385) baseStart_3711385 baseEnd_3711385 := by
    simpa [prefixWord, tailWord_3711385, baseEnd_3711385] using wordTrace_append hprefix tailTrace_3711385
  have hstable : (prefixWord ++ tailWord_3711385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711385).length < 2 ^ (prefixWord ++ tailWord_3711385).sum := by decide
  have hdescent : baseEnd_3711385 < baseStart_3711385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711446 : List Nat := [5, 2, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3711446 : Nat := 118140960795 + 3711446 * 2 ^ 59
def prefixEnd_3711446 : Nat := 4983230072969 + 3 ^ 40 * 3711446 * 2
def baseEnd_3711446 : Nat := 635251907068997061385459

theorem tailTrace_3711446 : CollatzResearch.WordTrace tailWord_3711446 prefixEnd_3711446 635251907068997061385459 := by
  unfold tailWord_3711446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460472282004530084836137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90245037674714987571585461 8460472282004530084836137)
  ·
    refine ⟨6345354211503397563627103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8460472282004530084836137 6345354211503397563627103)
    ·
      refine ⟨9518031317255096345440655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345354211503397563627103 9518031317255096345440655)
      ·
        refine ⟨14277046975882644518160983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9518031317255096345440655 14277046975882644518160983)
        ·
          refine ⟨21415570463823966777241475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14277046975882644518160983 21415570463823966777241475)
          ·
            refine ⟨32123355695735950165862213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21415570463823966777241475 32123355695735950165862213)
            ·
              refine ⟨6023129192950490656099165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32123355695735950165862213 6023129192950490656099165)
              ·
                refine ⟨2258673447356433996037187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6023129192950490656099165 2258673447356433996037187)
                ·
                  refine ⟨3388010171034650994055781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258673447356433996037187 3388010171034650994055781)
                  ·
                    refine ⟨635251907068997061385459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388010171034650994055781 635251907068997061385459)
                    ·
                      rfl

theorem cell23_3711446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3711446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711446 prefixEnd_3711446 := by exact prefixLift 3711446
  have htrace : WordTrace (prefixWord ++ tailWord_3711446) baseStart_3711446 baseEnd_3711446 := by
    simpa [prefixWord, tailWord_3711446, baseEnd_3711446] using wordTrace_append hprefix tailTrace_3711446
  have hstable : (prefixWord ++ tailWord_3711446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711446).length < 2 ^ (prefixWord ++ tailWord_3711446).sum := by decide
  have hdescent : baseEnd_3711446 < baseStart_3711446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711448 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3711448 : Nat := 118140960795 + 3711448 * 2 ^ 59
def prefixEnd_3711448 : Nat := 4983230072969 + 3 ^ 40 * 3711448 * 2
def baseEnd_3711448 : Nat := 1905756748168300176331367

theorem tailTrace_3711448 : CollatzResearch.WordTrace tailWord_3711448 prefixEnd_3711448 1905756748168300176331367 := by
  unfold tailWord_3711448
  simp only [CollatzResearch.WordTrace]
  refine ⟨67683814729032617849475499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90245086305376823799300665 67683814729032617849475499)
  ·
    refine ⟨101525722093548926774213249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67683814729032617849475499 101525722093548926774213249)
    ·
      refine ⟨76144291570161695080659937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101525722093548926774213249 76144291570161695080659937)
      ·
        refine ⟨57108218677621271310494953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76144291570161695080659937 57108218677621271310494953)
        ·
          refine ⟨42831164008215953482871215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57108218677621271310494953 42831164008215953482871215)
          ·
            refine ⟨64246746012323930224306823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42831164008215953482871215 64246746012323930224306823)
            ·
              refine ⟨96370119018485895336460235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64246746012323930224306823 96370119018485895336460235)
              ·
                refine ⟨144555178527728843004690353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96370119018485895336460235 144555178527728843004690353)
                ·
                  refine ⟨108416383895796632253517765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144555178527728843004690353 108416383895796632253517765)
                  ·
                    refine ⟨20328071980461868547534581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108416383895796632253517765 20328071980461868547534581)
                    ·
                      refine ⟨1905756748168300176331367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20328071980461868547534581 1905756748168300176331367)
                      ·
                        rfl

theorem cell23_3711448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3711448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711448 prefixEnd_3711448 := by exact prefixLift 3711448
  have htrace : WordTrace (prefixWord ++ tailWord_3711448) baseStart_3711448 baseEnd_3711448 := by
    simpa [prefixWord, tailWord_3711448, baseEnd_3711448] using wordTrace_append hprefix tailTrace_3711448
  have hstable : (prefixWord ++ tailWord_3711448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711448).length < 2 ^ (prefixWord ++ tailWord_3711448).sum := by decide
  have hdescent : baseEnd_3711448 < baseStart_3711448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711459 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 6]
def baseStart_3711459 : Nat := 118140960795 + 3711459 * 2 ^ 59
def prefixEnd_3711459 : Nat := 4983230072969 + 3 ^ 40 * 3711459 * 2
def baseEnd_3711459 : Nat := 211751377383944403699313

theorem tailTrace_3711459 : CollatzResearch.WordTrace tailWord_3711459 prefixEnd_3711459 211751377383944403699313 := by
  unfold tailWord_3711459
  simp only [CollatzResearch.WordTrace]
  refine ⟨135368030661025384577601431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90245353774016923051734287 135368030661025384577601431)
  ·
    refine ⟨203052045991538076866402147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135368030661025384577601431 203052045991538076866402147)
    ·
      refine ⟨304578068987307115299603221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203052045991538076866402147 304578068987307115299603221)
      ·
        refine ⟨14277096983780021029668901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304578068987307115299603221 14277096983780021029668901)
        ·
          refine ⟨2676955684458753943062919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14277096983780021029668901 2676955684458753943062919)
          ·
            refine ⟨4015433526688130914594379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676955684458753943062919 4015433526688130914594379)
            ·
              refine ⟨6023150290032196371891569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015433526688130914594379 6023150290032196371891569)
              ·
                refine ⟨4517362717524147278918677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6023150290032196371891569 4517362717524147278918677)
                ·
                  refine ⟨211751377383944403699313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4517362717524147278918677 211751377383944403699313)
                  ·
                    rfl

theorem cell23_3711459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 6].length) (baseStart_3711459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711459 prefixEnd_3711459 := by exact prefixLift 3711459
  have htrace : WordTrace (prefixWord ++ tailWord_3711459) baseStart_3711459 baseEnd_3711459 := by
    simpa [prefixWord, tailWord_3711459, baseEnd_3711459] using wordTrace_append hprefix tailTrace_3711459
  have hstable : (prefixWord ++ tailWord_3711459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711459).length < 2 ^ (prefixWord ++ tailWord_3711459).sum := by decide
  have hdescent : baseEnd_3711459 < baseStart_3711459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711469 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3711469 : Nat := 118140960795 + 3711469 * 2 ^ 59
def prefixEnd_3711469 : Nat := 4983230072969 + 3 ^ 40 * 3711469 * 2
def baseEnd_3711469 : Nat := 1905767531262044594168771

theorem tailTrace_3711469 : CollatzResearch.WordTrace tailWord_3711469 prefixEnd_3711469 1905767531262044594168771 := by
  unfold tailWord_3711469
  simp only [CollatzResearch.WordTrace]
  refine ⟨135368395390989156285465461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90245596927326104190310307 135368395390989156285465461)
  ·
    refine ⟨12690787067905233401762387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135368395390989156285465461 12690787067905233401762387)
    ·
      refine ⟨19036180601857850102643581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12690787067905233401762387 19036180601857850102643581)
      ·
        refine ⟨7138567725696693788491343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19036180601857850102643581 7138567725696693788491343)
        ·
          refine ⟨10707851588545040682737015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138567725696693788491343 10707851588545040682737015)
          ·
            refine ⟨16061777382817561024105523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10707851588545040682737015 16061777382817561024105523)
            ·
              refine ⟨24092666074226341536158285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16061777382817561024105523 24092666074226341536158285)
              ·
                refine ⟨9034749777834878076059357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24092666074226341536158285 9034749777834878076059357)
                ·
                  refine ⟨3388031166688079278522259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9034749777834878076059357 3388031166688079278522259)
                  ·
                    refine ⟨5082046750032118917783389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3388031166688079278522259 5082046750032118917783389)
                    ·
                      refine ⟨1905767531262044594168771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5082046750032118917783389 1905767531262044594168771)
                      ·
                        rfl

theorem cell23_3711469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3711469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711469 prefixEnd_3711469 := by exact prefixLift 3711469
  have htrace : WordTrace (prefixWord ++ tailWord_3711469) baseStart_3711469 baseEnd_3711469 := by
    simpa [prefixWord, tailWord_3711469, baseEnd_3711469] using wordTrace_append hprefix tailTrace_3711469
  have hstable : (prefixWord ++ tailWord_3711469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711469).length < 2 ^ (prefixWord ++ tailWord_3711469).sum := by decide
  have hdescent : baseEnd_3711469 < baseStart_3711469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711502 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_3711502 : Nat := 118140960795 + 3711502 * 2 ^ 59
def prefixEnd_3711502 : Nat := 4983230072969 + 3 ^ 40 * 3711502 * 2
def baseEnd_3711502 : Nat := 635261492041214321685373

theorem tailTrace_3711502 : CollatzResearch.WordTrace tailWord_3711502 prefixEnd_3711502 635261492041214321685373 := by
  unfold tailWord_3711502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921199874983700365177095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90246399333246401947611173 16921199874983700365177095)
  ·
    refine ⟨25381799812475550547765643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16921199874983700365177095 25381799812475550547765643)
    ·
      refine ⟨38072699718713325821648465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25381799812475550547765643 38072699718713325821648465)
      ·
        refine ⟨28554524789034994366236349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38072699718713325821648465 28554524789034994366236349)
        ·
          refine ⟨10707946795888122887338631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28554524789034994366236349 10707946795888122887338631)
          ·
            refine ⟨16061920193832184331007947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10707946795888122887338631 16061920193832184331007947)
            ·
              refine ⟨24092880290748276496511921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16061920193832184331007947 24092880290748276496511921)
              ·
                refine ⟨18069660218061207372383941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24092880290748276496511921 18069660218061207372383941)
                ·
                  refine ⟨3388061290886476382321989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18069660218061207372383941 3388061290886476382321989)
                  ·
                    refine ⟨635261492041214321685373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388061290886476382321989 635261492041214321685373)
                    ·
                      rfl

theorem cell23_3711502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_3711502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711502 prefixEnd_3711502 := by exact prefixLift 3711502
  have htrace : WordTrace (prefixWord ++ tailWord_3711502) baseStart_3711502 baseEnd_3711502 := by
    simpa [prefixWord, tailWord_3711502, baseEnd_3711502] using wordTrace_append hprefix tailTrace_3711502
  have hstable : (prefixWord ++ tailWord_3711502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711502).length < 2 ^ (prefixWord ++ tailWord_3711502).sum := by decide
  have hdescent : baseEnd_3711502 < baseStart_3711502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711512 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_3711512 : Nat := 118140960795 + 3711512 * 2 ^ 59
def prefixEnd_3711512 : Nat := 4983230072969 + 3 ^ 40 * 3711512 * 2
def baseEnd_3711512 : Nat := 1905789610930187925931073

theorem tailTrace_3711512 : CollatzResearch.WordTrace tailWord_3711512 prefixEnd_3711512 1905789610930187925931073 := by
  unfold tailWord_3711512
  simp only [CollatzResearch.WordTrace]
  refine ⟨67684981864916687314640395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90246642486555583086187193 67684981864916687314640395)
  ·
    refine ⟨101527472797375030971960593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67684981864916687314640395 101527472797375030971960593)
    ·
      refine ⟨76145604598031273228970445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101527472797375030971960593 76145604598031273228970445)
      ·
        refine ⟨28554601724261727460863917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76145604598031273228970445 28554601724261727460863917)
        ·
          refine ⟨10707975646598147797823969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28554601724261727460863917 10707975646598147797823969)
          ·
            refine ⟨8030981734948610848367977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10707975646598147797823969 8030981734948610848367977)
            ·
              refine ⟨6023236301211458136275983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8030981734948610848367977 6023236301211458136275983)
              ·
                refine ⟨9034854451817187204413975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023236301211458136275983 9034854451817187204413975)
                ·
                  refine ⟨13552281677725780806620963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9034854451817187204413975 13552281677725780806620963)
                  ·
                    refine ⟨20328422516588671209931445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13552281677725780806620963 20328422516588671209931445)
                    ·
                      refine ⟨1905789610930187925931073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20328422516588671209931445 1905789610930187925931073)
                      ·
                        rfl

theorem cell23_3711512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_3711512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711512 prefixEnd_3711512 := by exact prefixLift 3711512
  have htrace : WordTrace (prefixWord ++ tailWord_3711512) baseStart_3711512 baseEnd_3711512 := by
    simpa [prefixWord, tailWord_3711512, baseEnd_3711512] using wordTrace_append hprefix tailTrace_3711512
  have hstable : (prefixWord ++ tailWord_3711512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711512).length < 2 ^ (prefixWord ++ tailWord_3711512).sum := by decide
  have hdescent : baseEnd_3711512 < baseStart_3711512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711575 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 2, 6]
def baseStart_3711575 : Nat := 118140960795 + 3711575 * 2 ^ 59
def prefixEnd_3711575 : Nat := 4983230072969 + 3 ^ 40 * 3711575 * 2
def baseEnd_3711575 : Nat := 635273986737140393147761

theorem tailTrace_3711575 : CollatzResearch.WordTrace tailWord_3711575 prefixEnd_3711575 635273986737140393147761 := by
  unfold tailWord_3711575
  simp only [CollatzResearch.WordTrace]
  refine ⟨135372261528605136388824179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90248174352403424259216119 135372261528605136388824179)
  ·
    refine ⟨203058392292907704583236269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135372261528605136388824179 203058392292907704583236269)
    ·
      refine ⟨76146897109840389218713601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203058392292907704583236269 76146897109840389218713601)
      ·
        refine ⟨57110172832380291914035201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76146897109840389218713601 57110172832380291914035201)
        ·
          refine ⟨42832629624285218935526401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57110172832380291914035201 42832629624285218935526401)
          ·
            refine ⟨32124472218213914201644801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42832629624285218935526401 32124472218213914201644801)
            ·
              refine ⟨24093354163660435651233601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32124472218213914201644801 24093354163660435651233601)
              ·
                refine ⟨18070015622745326738425201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24093354163660435651233601 18070015622745326738425201)
                ·
                  refine ⟨13552511717058995053818901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18070015622745326738425201 13552511717058995053818901)
                  ·
                    refine ⟨635273986737140393147761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13552511717058995053818901 635273986737140393147761)
                    ·
                      rfl

theorem cell23_3711575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_3711575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711575 prefixEnd_3711575 := by exact prefixLift 3711575
  have htrace : WordTrace (prefixWord ++ tailWord_3711575) baseStart_3711575 baseEnd_3711575 := by
    simpa [prefixWord, tailWord_3711575, baseEnd_3711575] using wordTrace_append hprefix tailTrace_3711575
  have hstable : (prefixWord ++ tailWord_3711575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711575).length < 2 ^ (prefixWord ++ tailWord_3711575).sum := by decide
  have hdescent : baseEnd_3711575 < baseStart_3711575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711675 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5]
def baseStart_3711675 : Nat := 118140960795 + 3711675 * 2 ^ 59
def prefixEnd_3711675 : Nat := 4983230072969 + 3 ^ 40 * 3711675 * 2
def baseEnd_3711675 : Nat := 1905873308276870788192823

theorem tailTrace_3711675 : CollatzResearch.WordTrace tailWord_3711675 prefixEnd_3711675 1905873308276870788192823 := by
  unfold tailWord_3711675
  simp only [CollatzResearch.WordTrace]
  refine ⟨135375908828242853467464479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90250605885495235644976319 135375908828242853467464479)
  ·
    refine ⟨203063863242364280201196719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135375908828242853467464479 203063863242364280201196719)
    ·
      refine ⟨304595794863546420301795079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203063863242364280201196719 304595794863546420301795079)
      ·
        refine ⟨456893692295319630452692619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304595794863546420301795079 456893692295319630452692619)
        ·
          refine ⟨685340538442979445679038929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456893692295319630452692619 685340538442979445679038929)
          ·
            refine ⟨514005403832234584259279197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685340538442979445679038929 514005403832234584259279197)
            ·
              refine ⟨192752026437087969097229699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514005403832234584259279197 192752026437087969097229699)
              ·
                refine ⟨289128039655631953645844549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192752026437087969097229699 289128039655631953645844549)
                ·
                  refine ⟨54211507435430991308595853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289128039655631953645844549 54211507435430991308595853)
                  ·
                    refine ⟨20329315288286621740723445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54211507435430991308595853 20329315288286621740723445)
                    ·
                      refine ⟨1905873308276870788192823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20329315288286621740723445 1905873308276870788192823)
                      ·
                        rfl

theorem cell23_3711675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_3711675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711675 prefixEnd_3711675 := by exact prefixLift 3711675
  have htrace : WordTrace (prefixWord ++ tailWord_3711675) baseStart_3711675 baseEnd_3711675 := by
    simpa [prefixWord, tailWord_3711675, baseEnd_3711675] using wordTrace_append hprefix tailTrace_3711675
  have hstable : (prefixWord ++ tailWord_3711675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711675).length < 2 ^ (prefixWord ++ tailWord_3711675).sum := by decide
  have hdescent : baseEnd_3711675 < baseStart_3711675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711726 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_3711726 : Nat := 118140960795 + 3711726 * 2 ^ 59
def prefixEnd_3711726 : Nat := 4983230072969 + 3 ^ 40 * 3711726 * 2
def baseEnd_3711726 : Nat := 1905899495790250088655089

theorem tailTrace_3711726 : CollatzResearch.WordTrace tailWord_3711726 prefixEnd_3711726 1905899495790250088655089 := by
  unfold tailWord_3711726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922221118882261147196379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90251845967372059451714021 16922221118882261147196379)
  ·
    refine ⟨25383331678323391720794569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16922221118882261147196379 25383331678323391720794569)
    ·
      refine ⟨19037498758742543790595927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25383331678323391720794569 19037498758742543790595927)
      ·
        refine ⟨28556248138113815685893891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19037498758742543790595927 28556248138113815685893891)
        ·
          refine ⟨42834372207170723528840837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28556248138113815685893891 42834372207170723528840837)
          ·
            refine ⟨8031444788844510661657657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42834372207170723528840837 8031444788844510661657657)
            ·
              refine ⟨6023583591633382996243243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8031444788844510661657657 6023583591633382996243243)
              ·
                refine ⟨9035375387450074494364865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023583591633382996243243 9035375387450074494364865)
                ·
                  refine ⟨6776531540587555870773649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9035375387450074494364865 6776531540587555870773649)
                  ·
                    refine ⟨5082398655440666903080237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6776531540587555870773649 5082398655440666903080237)
                    ·
                      refine ⟨1905899495790250088655089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5082398655440666903080237 1905899495790250088655089)
                      ·
                        rfl

theorem cell23_3711726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_3711726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711726 prefixEnd_3711726 := by exact prefixLift 3711726
  have htrace : WordTrace (prefixWord ++ tailWord_3711726) baseStart_3711726 baseEnd_3711726 := by
    simpa [prefixWord, tailWord_3711726, baseEnd_3711726] using wordTrace_append hprefix tailTrace_3711726
  have hstable : (prefixWord ++ tailWord_3711726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711726).length < 2 ^ (prefixWord ++ tailWord_3711726).sum := by decide
  have hdescent : baseEnd_3711726 < baseStart_3711726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711746 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3711746 : Nat := 118140960795 + 3711746 * 2 ^ 59
def prefixEnd_3711746 : Nat := 4983230072969 + 3 ^ 40 * 3711746 * 2
def baseEnd_3711746 : Nat := 211767751711482223378333

theorem tailTrace_3711746 : CollatzResearch.WordTrace tailWord_3711746 prefixEnd_3711746 211767751711482223378333 := by
  unfold tailWord_3711746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33844624602746408148324773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90252332273990421728866061 33844624602746408148324773)
  ·
    refine ⟨6345867113014951527810895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33844624602746408148324773 6345867113014951527810895)
    ·
      refine ⟨9518800669522427291716343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345867113014951527810895 9518800669522427291716343)
      ·
        refine ⟨14278201004283640937574515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9518800669522427291716343 14278201004283640937574515)
        ·
          refine ⟨21417301506425461406361773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14278201004283640937574515 21417301506425461406361773)
          ·
            refine ⟨8031488064909548027385665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21417301506425461406361773 8031488064909548027385665)
            ·
              refine ⟨6023616048682161020539249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8031488064909548027385665 6023616048682161020539249)
              ·
                refine ⟨4517712036511620765404437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6023616048682161020539249 4517712036511620765404437)
                ·
                  refine ⟨211767751711482223378333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4517712036511620765404437 211767751711482223378333)
                  ·
                    rfl

theorem cell23_3711746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3711746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711746 prefixEnd_3711746 := by exact prefixLift 3711746
  have htrace : WordTrace (prefixWord ++ tailWord_3711746) baseStart_3711746 baseEnd_3711746 := by
    simpa [prefixWord, tailWord_3711746, baseEnd_3711746] using wordTrace_append hprefix tailTrace_3711746
  have hstable : (prefixWord ++ tailWord_3711746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711746).length < 2 ^ (prefixWord ++ tailWord_3711746).sum := by decide
  have hdescent : baseEnd_3711746 < baseStart_3711746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711779 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 4]
def baseStart_3711779 : Nat := 118140960795 + 3711779 * 2 ^ 59
def prefixEnd_3711779 : Nat := 4983230072969 + 3 ^ 40 * 3711779 * 2
def baseEnd_3711779 : Nat := 1905926710264938381292345

theorem tailTrace_3711779 : CollatzResearch.WordTrace tailWord_3711779 prefixEnd_3711779 1905926710264938381292345 := by
  unfold tailWord_3711779
  simp only [CollatzResearch.WordTrace]
  refine ⟨135379702019866079229250391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90253134679910719486166927 135379702019866079229250391)
  ·
    refine ⟨203069553029799118843875587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135379702019866079229250391 203069553029799118843875587)
    ·
      refine ⟨304604329544698678265813381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203069553029799118843875587 304604329544698678265813381)
      ·
        refine ⟨57113311789631002174840009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304604329544698678265813381 57113311789631002174840009)
        ·
          refine ⟨42834983842223251631130007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57113311789631002174840009 42834983842223251631130007)
          ·
            refine ⟨64252475763334877446695011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42834983842223251631130007 64252475763334877446695011)
            ·
              refine ⟨96378713645002316170042517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64252475763334877446695011 96378713645002316170042517)
              ·
                refine ⟨4517752202109483570470743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96378713645002316170042517 4517752202109483570470743)
                ·
                  refine ⟨6776628303164225355706115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517752202109483570470743 6776628303164225355706115)
                  ·
                    refine ⟨10164942454746338033559173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776628303164225355706115 10164942454746338033559173)
                    ·
                      refine ⟨1905926710264938381292345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10164942454746338033559173 1905926710264938381292345)
                      ·
                        rfl

theorem cell23_3711779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_3711779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711779 prefixEnd_3711779 := by exact prefixLift 3711779
  have htrace : WordTrace (prefixWord ++ tailWord_3711779) baseStart_3711779 baseEnd_3711779 := by
    simpa [prefixWord, tailWord_3711779, baseEnd_3711779] using wordTrace_append hprefix tailTrace_3711779
  have hstable : (prefixWord ++ tailWord_3711779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711779).length < 2 ^ (prefixWord ++ tailWord_3711779).sum := by decide
  have hdescent : baseEnd_3711779 < baseStart_3711779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711790 : List Nat := [4, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3711790 : Nat := 118140960795 + 3711790 * 2 ^ 59
def prefixEnd_3711790 : Nat := 4983230072969 + 3 ^ 40 * 3711790 * 2
def baseEnd_3711790 : Nat := 1905932358552137838254795

theorem tailTrace_3711790 : CollatzResearch.WordTrace tailWord_3711790 prefixEnd_3711790 1905932358552137838254795 := by
  unfold tailWord_3711790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922512902853278513487603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90253402148550818738600549 16922512902853278513487603)
  ·
    refine ⟨25383769354279917770231405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16922512902853278513487603 25383769354279917770231405)
    ·
      refine ⟨9518913507854969163836777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25383769354279917770231405 9518913507854969163836777)
      ·
        refine ⟨7139185130891226872877583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9518913507854969163836777 7139185130891226872877583)
        ·
          refine ⟨10708777696336840309316375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139185130891226872877583 10708777696336840309316375)
          ·
            refine ⟨16063166544505260463974563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10708777696336840309316375 16063166544505260463974563)
            ·
              refine ⟨24094749816757890695961845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16063166544505260463974563 24094749816757890695961845)
              ·
                refine ⟨2258882795321052252746423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24094749816757890695961845 2258882795321052252746423)
                ·
                  refine ⟨3388324192981578379119635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258882795321052252746423 3388324192981578379119635)
                  ·
                    refine ⟨5082486289472367568679453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3388324192981578379119635 5082486289472367568679453)
                    ·
                      refine ⟨1905932358552137838254795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5082486289472367568679453 1905932358552137838254795)
                      ·
                        rfl

theorem cell23_3711790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3711790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711790 prefixEnd_3711790 := by exact prefixLift 3711790
  have htrace : WordTrace (prefixWord ++ tailWord_3711790) baseStart_3711790 baseEnd_3711790 := by
    simpa [prefixWord, tailWord_3711790, baseEnd_3711790] using wordTrace_append hprefix tailTrace_3711790
  have hstable : (prefixWord ++ tailWord_3711790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711790).length < 2 ^ (prefixWord ++ tailWord_3711790).sum := by decide
  have hdescent : baseEnd_3711790 < baseStart_3711790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711832 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 2, 7]
def baseStart_3711832 : Nat := 118140960795 + 3711832 * 2 ^ 59
def prefixEnd_3711832 : Nat := 4983230072969 + 3 ^ 40 * 3711832 * 2
def baseEnd_3711832 : Nat := 635317974913208891309867

theorem tailTrace_3711832 : CollatzResearch.WordTrace tailWord_3711832 prefixEnd_3711832 635317974913208891309867 := by
  unfold tailWord_3711832
  simp only [CollatzResearch.WordTrace]
  refine ⟨67690817544337034640464875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90254423392449379520619833 67690817544337034640464875)
  ·
    refine ⟨101536226316505551960697313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67690817544337034640464875 101536226316505551960697313)
    ·
      refine ⟨76152169737379163970522985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101536226316505551960697313 76152169737379163970522985)
      ·
        refine ⟨57114127303034372977892239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76152169737379163970522985 57114127303034372977892239)
        ·
          refine ⟨85671190954551559466838359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57114127303034372977892239 85671190954551559466838359)
          ·
            refine ⟨128506786431827339200257539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85671190954551559466838359 128506786431827339200257539)
            ·
              refine ⟨192760179647741008800386309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128506786431827339200257539 192760179647741008800386309)
              ·
                refine ⟨36142533683951439150072433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192760179647741008800386309 36142533683951439150072433)
                ·
                  refine ⟨27106900262963579362554325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36142533683951439150072433 27106900262963579362554325)
                  ·
                    refine ⟨635317974913208891309867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27106900262963579362554325 635317974913208891309867)
                    ·
                      rfl

theorem cell23_3711832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_3711832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711832 prefixEnd_3711832 := by exact prefixLift 3711832
  have htrace : WordTrace (prefixWord ++ tailWord_3711832) baseStart_3711832 baseEnd_3711832 := by
    simpa [prefixWord, tailWord_3711832, baseEnd_3711832] using wordTrace_append hprefix tailTrace_3711832
  have hstable : (prefixWord ++ tailWord_3711832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711832).length < 2 ^ (prefixWord ++ tailWord_3711832).sum := by decide
  have hdescent : baseEnd_3711832 < baseStart_3711832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711836 : List Nat := [2, 2, 4, 2, 1, 1, 4, 7]
def baseStart_3711836 : Nat := 118140960795 + 3711836 * 2 ^ 59
def prefixEnd_3711836 : Nat := 4983230072969 + 3 ^ 40 * 3711836 * 2
def baseEnd_3711836 : Nat := 70590962172675728084429

theorem tailTrace_3711836 : CollatzResearch.WordTrace tailWord_3711836 prefixEnd_3711836 70590962172675728084429 := by
  unfold tailWord_3711836
  simp only [CollatzResearch.WordTrace]
  refine ⟨67690890490329788982037681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90254520653773051976050241 67690890490329788982037681)
  ·
    refine ⟨50768167867747341736528261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67690890490329788982037681 50768167867747341736528261)
    ·
      refine ⟨9519031475202626575599049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50768167867747341736528261 9519031475202626575599049)
      ·
        refine ⟨7139273606401969931699287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9519031475202626575599049 7139273606401969931699287)
        ·
          refine ⟨10708910409602954897548931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139273606401969931699287 10708910409602954897548931)
          ·
            refine ⟨16063365614404432346323397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10708910409602954897548931 16063365614404432346323397)
            ·
              refine ⟨3011881052700831064935637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16063365614404432346323397 3011881052700831064935637)
              ·
                refine ⟨70590962172675728084429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3011881052700831064935637 70590962172675728084429)
                ·
                  rfl

theorem cell23_3711836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 7].length) (baseStart_3711836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711836 prefixEnd_3711836 := by exact prefixLift 3711836
  have htrace : WordTrace (prefixWord ++ tailWord_3711836) baseStart_3711836 baseEnd_3711836 := by
    simpa [prefixWord, tailWord_3711836, baseEnd_3711836] using wordTrace_append hprefix tailTrace_3711836
  have hstable : (prefixWord ++ tailWord_3711836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711836).length < 2 ^ (prefixWord ++ tailWord_3711836).sum := by decide
  have hdescent : baseEnd_3711836 < baseStart_3711836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711847 : List Nat := [1, 1, 5, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_3711847 : Nat := 118140960795 + 3711847 * 2 ^ 59
def prefixEnd_3711847 : Nat := 4983230072969 + 3 ^ 40 * 3711847 * 2
def baseEnd_3711847 : Nat := 1905961626949444115242033

theorem tailTrace_3711847 : CollatzResearch.WordTrace tailWord_3711847 prefixEnd_3711847 1905961626949444115242033 := by
  unfold tailWord_3711847
  simp only [CollatzResearch.WordTrace]
  refine ⟨135382182183619726842725795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90254788122413151228483863 135382182183619726842725795)
  ·
    refine ⟨203073273275429590264088693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135382182183619726842725795 203073273275429590264088693)
    ·
      refine ⟨19038119369571524087258315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203073273275429590264088693 19038119369571524087258315)
      ·
        refine ⟨28557179054357286130887473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19038119369571524087258315 28557179054357286130887473)
        ·
          refine ⟨21417884290767964598165605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28557179054357286130887473 21417884290767964598165605)
          ·
            refine ⟨4015853304518993362156051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21417884290767964598165605 4015853304518993362156051)
            ·
              refine ⟨6023779956778490043234077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015853304518993362156051 6023779956778490043234077)
              ·
                refine ⟨2258917483791933766212779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6023779956778490043234077 2258917483791933766212779)
                ·
                  refine ⟨3388376225687900649319169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258917483791933766212779 3388376225687900649319169)
                  ·
                    refine ⟨2541282169265925486989377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3388376225687900649319169 2541282169265925486989377)
                    ·
                      refine ⟨1905961626949444115242033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541282169265925486989377 1905961626949444115242033)
                      ·
                        rfl

theorem cell23_3711847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_3711847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711847 prefixEnd_3711847 := by exact prefixLift 3711847
  have htrace : WordTrace (prefixWord ++ tailWord_3711847) baseStart_3711847 baseEnd_3711847 := by
    simpa [prefixWord, tailWord_3711847, baseEnd_3711847] using wordTrace_append hprefix tailTrace_3711847
  have hstable : (prefixWord ++ tailWord_3711847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711847).length < 2 ^ (prefixWord ++ tailWord_3711847).sum := by decide
  have hdescent : baseEnd_3711847 < baseStart_3711847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711874 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3711874 : Nat := 118140960795 + 3711874 * 2 ^ 59
def prefixEnd_3711874 : Nat := 4983230072969 + 3 ^ 40 * 3711874 * 2
def baseEnd_3711874 : Nat := 635325163642371836534803

theorem tailTrace_3711874 : CollatzResearch.WordTrace tailWord_3711874 prefixEnd_3711874 635325163642371836534803 := by
  unfold tailWord_3711874
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845791738630477613489669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90255444636347940302639117 33845791738630477613489669)
  ·
    refine ⟨6346085950993214552529313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33845791738630477613489669 6346085950993214552529313)
    ·
      refine ⟨4759564463244910914396985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6346085950993214552529313 4759564463244910914396985)
      ·
        refine ⟨3569673347433683185797739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4759564463244910914396985 3569673347433683185797739)
        ·
          refine ⟨5354510021150524778696609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569673347433683185797739 5354510021150524778696609)
          ·
            refine ⟨4015882515862893584022457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5354510021150524778696609 4015882515862893584022457)
            ·
              refine ⟨3011911886897170188016843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015882515862893584022457 3011911886897170188016843)
              ·
                refine ⟨4517867830345755282025265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011911886897170188016843 4517867830345755282025265)
                ·
                  refine ⟨3388400872759316461518949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4517867830345755282025265 3388400872759316461518949)
                  ·
                    refine ⟨635325163642371836534803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388400872759316461518949 635325163642371836534803)
                    ·
                      rfl

theorem cell23_3711874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3711874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711874 prefixEnd_3711874 := by exact prefixLift 3711874
  have htrace : WordTrace (prefixWord ++ tailWord_3711874) baseStart_3711874 baseEnd_3711874 := by
    simpa [prefixWord, tailWord_3711874, baseEnd_3711874] using wordTrace_append hprefix tailTrace_3711874
  have hstable : (prefixWord ++ tailWord_3711874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711874).length < 2 ^ (prefixWord ++ tailWord_3711874).sum := by decide
  have hdescent : baseEnd_3711874 < baseStart_3711874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711880 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3711880 : Nat := 118140960795 + 3711880 * 2 ^ 59
def prefixEnd_3711880 : Nat := 4983230072969 + 3 ^ 40 * 3711880 * 2
def baseEnd_3711880 : Nat := 1905978571811042486129381

theorem tailTrace_3711880 : CollatzResearch.WordTrace tailWord_3711880 prefixEnd_3711880 1905978571811042486129381 := by
  unfold tailWord_3711880
  simp only [CollatzResearch.WordTrace]
  refine ⟨67691692896250086739338547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90255590528333448985784729 67691692896250086739338547)
  ·
    refine ⟨101537539344375130109007821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67691692896250086739338547 101537539344375130109007821)
    ·
      refine ⟨38076577254140673790877933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101537539344375130109007821 38076577254140673790877933)
      ·
        refine ⟨14278716470302752671579225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38076577254140673790877933 14278716470302752671579225)
        ·
          refine ⟨10709037352727064503684419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14278716470302752671579225 10709037352727064503684419)
          ·
            refine ⟨16063556029090596755526629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709037352727064503684419 16063556029090596755526629)
            ·
              refine ⟨3011916755454486891661243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16063556029090596755526629 3011916755454486891661243)
              ·
                refine ⟨4517875133181730337491865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011916755454486891661243 4517875133181730337491865)
                ·
                  refine ⟨3388406349886297753118899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4517875133181730337491865 3388406349886297753118899)
                  ·
                    refine ⟨5082609524829446629678349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3388406349886297753118899 5082609524829446629678349)
                    ·
                      refine ⟨1905978571811042486129381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5082609524829446629678349 1905978571811042486129381)
                      ·
                        rfl

theorem cell23_3711880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3711880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711880 prefixEnd_3711880 := by exact prefixLift 3711880
  have htrace : WordTrace (prefixWord ++ tailWord_3711880) baseStart_3711880 baseEnd_3711880 := by
    simpa [prefixWord, tailWord_3711880, baseEnd_3711880] using wordTrace_append hprefix tailTrace_3711880
  have hstable : (prefixWord ++ tailWord_3711880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711880).length < 2 ^ (prefixWord ++ tailWord_3711880).sum := by decide
  have hdescent : baseEnd_3711880 < baseStart_3711880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711890 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3711890 : Nat := 118140960795 + 3711890 * 2 ^ 59
def prefixEnd_3711890 : Nat := 4983230072969 + 3 ^ 40 * 3711890 * 2
def baseEnd_3711890 : Nat := 1905983706617587447004335

theorem tailTrace_3711890 : CollatzResearch.WordTrace tailWord_3711890 prefixEnd_3711890 1905983706617587447004335 := by
  unfold tailWord_3711890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845937630615986296635281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90255833681642630124360749 33845937630615986296635281)
  ·
    refine ⟨25384453222961989722476461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33845937630615986296635281 25384453222961989722476461)
    ·
      refine ⟨9519169958610746145928673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25384453222961989722476461 9519169958610746145928673)
      ·
        refine ⟨7139377468958059609446505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9519169958610746145928673 7139377468958059609446505)
        ·
          refine ⟨5354533101718544707084879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7139377468958059609446505 5354533101718544707084879)
          ·
            refine ⟨8031799652577817060627319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354533101718544707084879 8031799652577817060627319)
            ·
              refine ⟨12047699478866725590940979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031799652577817060627319 12047699478866725590940979)
              ·
                refine ⟨18071549218300088386411469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047699478866725590940979 18071549218300088386411469)
                ·
                  refine ⟨6776830956862533144904301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18071549218300088386411469 6776830956862533144904301)
                  ·
                    refine ⟨2541311608823449929339113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6776830956862533144904301 2541311608823449929339113)
                    ·
                      refine ⟨1905983706617587447004335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541311608823449929339113 1905983706617587447004335)
                      ·
                        rfl

theorem cell23_3711890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3711890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711890 prefixEnd_3711890 := by exact prefixLift 3711890
  have htrace : WordTrace (prefixWord ++ tailWord_3711890) baseStart_3711890 baseEnd_3711890 := by
    simpa [prefixWord, tailWord_3711890, baseEnd_3711890] using wordTrace_append hprefix tailTrace_3711890
  have hstable : (prefixWord ++ tailWord_3711890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711890).length < 2 ^ (prefixWord ++ tailWord_3711890).sum := by decide
  have hdescent : baseEnd_3711890 < baseStart_3711890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711903 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 1, 4, 2]
def baseStart_3711903 : Nat := 118140960795 + 3711903 * 2 ^ 59
def prefixEnd_3711903 : Nat := 4983230072969 + 3 ^ 40 * 3711903 * 2
def baseEnd_3711903 : Nat := 1905990381866095896141775

theorem tailTrace_3711903 : CollatzResearch.WordTrace tailWord_3711903 prefixEnd_3711903 1905990381866095896141775 := by
  unfold tailWord_3711903
  simp only [CollatzResearch.WordTrace]
  refine ⟨135384224671416848406764363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90256149780944565604509575 135384224671416848406764363)
  ·
    refine ⟨203076337007125272610146545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135384224671416848406764363 203076337007125272610146545)
    ·
      refine ⟨152307252755343954457609909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203076337007125272610146545 152307252755343954457609909)
      ·
        refine ⟨14278804945813495730400929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152307252755343954457609909 14278804945813495730400929)
        ·
          refine ⟨10709103709360121797800697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14278804945813495730400929 10709103709360121797800697)
          ·
            refine ⟨8031827782020091348350523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709103709360121797800697 8031827782020091348350523)
            ·
              refine ⟨12047741673030137022525785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031827782020091348350523 12047741673030137022525785)
              ·
                refine ⟨9035806254772602766894339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12047741673030137022525785 9035806254772602766894339)
                ·
                  refine ⟨13553709382158904150341509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9035806254772602766894339 13553709382158904150341509)
                  ·
                    refine ⟨2541320509154794528189033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13553709382158904150341509 2541320509154794528189033)
                    ·
                      refine ⟨1905990381866095896141775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541320509154794528189033 1905990381866095896141775)
                      ·
                        rfl

theorem cell23_3711903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_3711903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711903 prefixEnd_3711903 := by exact prefixLift 3711903
  have htrace : WordTrace (prefixWord ++ tailWord_3711903) baseStart_3711903 baseEnd_3711903 := by
    simpa [prefixWord, tailWord_3711903, baseEnd_3711903] using wordTrace_append hprefix tailTrace_3711903
  have hstable : (prefixWord ++ tailWord_3711903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711903).length < 2 ^ (prefixWord ++ tailWord_3711903).sum := by decide
  have hdescent : baseEnd_3711903 < baseStart_3711903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711906 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3711906 : Nat := 118140960795 + 3711906 * 2 ^ 59
def prefixEnd_3711906 : Nat := 4983230072969 + 3 ^ 40 * 3711906 * 2
def baseEnd_3711906 : Nat := 1905991922308059384404261

theorem tailTrace_3711906 : CollatzResearch.WordTrace tailWord_3711906 prefixEnd_3711906 1905991922308059384404261 := by
  unfold tailWord_3711906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33846083522601494979780893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90256222726937319946082381 33846083522601494979780893)
  ·
    refine ⟨12692281320975560617417835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33846083522601494979780893 12692281320975560617417835)
    ·
      refine ⟨19038421981463340926126753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692281320975560617417835 19038421981463340926126753)
      ·
        refine ⟨14278816486097505694595065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19038421981463340926126753 14278816486097505694595065)
        ·
          refine ⟨10709112364573129270946299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14278816486097505694595065 10709112364573129270946299)
          ·
            refine ⟨16063668546859693906419449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709112364573129270946299 16063668546859693906419449)
            ·
              refine ⟨12047751410144770429814587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16063668546859693906419449 12047751410144770429814587)
              ·
                refine ⟨18071627115217155644721881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047751410144770429814587 18071627115217155644721881)
                ·
                  refine ⟨13553720336412866733541411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18071627115217155644721881 13553720336412866733541411)
                  ·
                    refine ⟨20330580504619300100312117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13553720336412866733541411 20330580504619300100312117)
                    ·
                      refine ⟨1905991922308059384404261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20330580504619300100312117 1905991922308059384404261)
                      ·
                        rfl

theorem cell23_3711906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3711906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711906 prefixEnd_3711906 := by exact prefixLift 3711906
  have htrace : WordTrace (prefixWord ++ tailWord_3711906) baseStart_3711906 baseEnd_3711906 := by
    simpa [prefixWord, tailWord_3711906, baseEnd_3711906] using wordTrace_append hprefix tailTrace_3711906
  have hstable : (prefixWord ++ tailWord_3711906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711906).length < 2 ^ (prefixWord ++ tailWord_3711906).sum := by decide
  have hdescent : baseEnd_3711906 < baseStart_3711906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711936 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3]
def baseStart_3711936 : Nat := 118140960795 + 3711936 * 2 ^ 59
def prefixEnd_3711936 : Nat := 4983230072969 + 3 ^ 40 * 3711936 * 2
def baseEnd_3711936 : Nat := 1906007326727694267029123

theorem tailTrace_3711936 : CollatzResearch.WordTrace tailWord_3711936 prefixEnd_3711936 1906007326727694267029123 := by
  unfold tailWord_3711936
  simp only [CollatzResearch.WordTrace]
  refine ⟨67692714140148647521357831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90256952186864863361810441 67692714140148647521357831)
  ·
    refine ⟨101539071210222971282036747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67692714140148647521357831 101539071210222971282036747)
    ·
      refine ⟨152308606815334456923055121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101539071210222971282036747 152308606815334456923055121)
      ·
        refine ⟨114231455111500842692291341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152308606815334456923055121 114231455111500842692291341)
        ·
          refine ⟨42836795666812816009609253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114231455111500842692291341 42836795666812816009609253)
          ·
            refine ⟨8031899187527403001801735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42836795666812816009609253 8031899187527403001801735)
            ·
              refine ⟨12047848781291104502702603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031899187527403001801735 12047848781291104502702603)
              ·
                refine ⟨18071773171936656754053905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047848781291104502702603 18071773171936656754053905)
                ·
                  refine ⟨13553829878952492565540429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18071773171936656754053905 13553829878952492565540429)
                  ·
                    refine ⟨5082686204607184712077661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13553829878952492565540429 5082686204607184712077661)
                    ·
                      refine ⟨1906007326727694267029123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5082686204607184712077661 1906007326727694267029123)
                      ·
                        rfl

theorem cell23_3711936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_3711936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711936 prefixEnd_3711936 := by exact prefixLift 3711936
  have htrace : WordTrace (prefixWord ++ tailWord_3711936) baseStart_3711936 baseEnd_3711936 := by
    simpa [prefixWord, tailWord_3711936, baseEnd_3711936] using wordTrace_append hprefix tailTrace_3711936
  have hstable : (prefixWord ++ tailWord_3711936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711936).length < 2 ^ (prefixWord ++ tailWord_3711936).sum := by decide
  have hdescent : baseEnd_3711936 < baseStart_3711936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711946 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_3711946 : Nat := 118140960795 + 3711946 * 2 ^ 59
def prefixEnd_3711946 : Nat := 4983230072969 + 3 ^ 40 * 3711946 * 2
def baseEnd_3711946 : Nat := 1906012461534239227904077

theorem tailTrace_3711946 : CollatzResearch.WordTrace tailWord_3711946 prefixEnd_3711946 1906012461534239227904077 := by
  unfold tailWord_3711946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33846448252565266687644923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90257195340174044500386461 33846448252565266687644923)
  ·
    refine ⟨50769672378847900031467385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33846448252565266687644923 50769672378847900031467385)
    ·
      refine ⟨38077254284135925023600539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50769672378847900031467385 38077254284135925023600539)
      ·
        refine ⟨57115881426203887535400809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38077254284135925023600539 57115881426203887535400809)
        ·
          refine ⟨42836911069652915651550607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57115881426203887535400809 42836911069652915651550607)
          ·
            refine ⟨64255366604479373477325911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42836911069652915651550607 64255366604479373477325911)
            ·
              refine ⟨96383049906719060215988867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64255366604479373477325911 96383049906719060215988867)
              ·
                refine ⟨144574574860078590323983301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96383049906719060215988867 144574574860078590323983301)
                ·
                  refine ⟨27107732786264735685746869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144574574860078590323983301 27107732786264735685746869)
                  ·
                    refine ⟨2541349948712318970538769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27107732786264735685746869 2541349948712318970538769)
                    ·
                      refine ⟨1906012461534239227904077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541349948712318970538769 1906012461534239227904077)
                      ·
                        rfl

theorem cell23_3711946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_3711946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711946 prefixEnd_3711946 := by exact prefixLift 3711946
  have htrace : WordTrace (prefixWord ++ tailWord_3711946) baseStart_3711946 baseEnd_3711946 := by
    simpa [prefixWord, tailWord_3711946, baseEnd_3711946] using wordTrace_append hprefix tailTrace_3711946
  have hstable : (prefixWord ++ tailWord_3711946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711946).length < 2 ^ (prefixWord ++ tailWord_3711946).sum := by decide
  have hdescent : baseEnd_3711946 < baseStart_3711946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711956 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_3711956 : Nat := 118140960795 + 3711956 * 2 ^ 59
def prefixEnd_3711956 : Nat := 4983230072969 + 3 ^ 40 * 3711956 * 2
def baseEnd_3711956 : Nat := 635339198780261396259677

theorem tailTrace_3711956 : CollatzResearch.WordTrace tailWord_3711956 prefixEnd_3711956 635339198780261396259677 := by
  unfold tailWord_3711956
  simp only [CollatzResearch.WordTrace]
  refine ⟨67693078870112419229221861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90257438493483225638962481 67693078870112419229221861)
  ·
    refine ⟨12692452288146078605479099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67693078870112419229221861 12692452288146078605479099)
    ·
      refine ⟨19038678432219117908218649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692452288146078605479099 19038678432219117908218649)
      ·
        refine ⟨14279008824164338431163987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19038678432219117908218649 14279008824164338431163987)
        ·
          refine ⟨21418513236246507646745981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14279008824164338431163987 21418513236246507646745981)
          ·
            refine ⟨8031942463592440367529743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21418513236246507646745981 8031942463592440367529743)
            ·
              refine ⟨12047913695388660551294615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031942463592440367529743 12047913695388660551294615)
              ·
                refine ⟨18071870543082990826941923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047913695388660551294615 18071870543082990826941923)
                ·
                  refine ⟨27107805814624486240412885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18071870543082990826941923 27107805814624486240412885)
                  ·
                    refine ⟨635339198780261396259677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27107805814624486240412885 635339198780261396259677)
                    ·
                      rfl

theorem cell23_3711956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_3711956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711956 prefixEnd_3711956 := by exact prefixLift 3711956
  have htrace : WordTrace (prefixWord ++ tailWord_3711956) baseStart_3711956 baseEnd_3711956 := by
    simpa [prefixWord, tailWord_3711956, baseEnd_3711956] using wordTrace_append hprefix tailTrace_3711956
  have hstable : (prefixWord ++ tailWord_3711956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711956).length < 2 ^ (prefixWord ++ tailWord_3711956).sum := by decide
  have hdescent : baseEnd_3711956 < baseStart_3711956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711976 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3711976 : Nat := 118140960795 + 3711976 * 2 ^ 59
def prefixEnd_3711976 : Nat := 4983230072969 + 3 ^ 40 * 3711976 * 2
def baseEnd_3711976 : Nat := 1906027865953874110528939

theorem tailTrace_3711976 : CollatzResearch.WordTrace tailWord_3711976 prefixEnd_3711976 1906027865953874110528939 := by
  unfold tailWord_3711976
  simp only [CollatzResearch.WordTrace]
  refine ⟨67693443600076190937085891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90257924800101587916114521 67693443600076190937085891)
  ·
    refine ⟨101540165400114286405628837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67693443600076190937085891 101540165400114286405628837)
    ·
      refine ⟨19038781012521428701055407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101540165400114286405628837 19038781012521428701055407)
      ·
        refine ⟨28558171518782143051583111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19038781012521428701055407 28558171518782143051583111)
        ·
          refine ⟨42837257278173214577374667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28558171518782143051583111 42837257278173214577374667)
          ·
            refine ⟨64255885917259821866062001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42837257278173214577374667 64255885917259821866062001)
            ·
              refine ⟨48191914437944866399546501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64255885917259821866062001 48191914437944866399546501)
              ·
                refine ⟨9035983957114662449914969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48191914437944866399546501 9035983957114662449914969)
                ·
                  refine ⟨6776987967835996837436227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9035983957114662449914969 6776987967835996837436227)
                  ·
                    refine ⟨10165481951753995256154341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776987967835996837436227 10165481951753995256154341)
                    ·
                      refine ⟨1906027865953874110528939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10165481951753995256154341 1906027865953874110528939)
                      ·
                        rfl

theorem cell23_3711976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3711976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711976 prefixEnd_3711976 := by exact prefixLift 3711976
  have htrace : WordTrace (prefixWord ++ tailWord_3711976) baseStart_3711976 baseEnd_3711976 := by
    simpa [prefixWord, tailWord_3711976, baseEnd_3711976] using wordTrace_append hprefix tailTrace_3711976
  have hstable : (prefixWord ++ tailWord_3711976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711976).length < 2 ^ (prefixWord ++ tailWord_3711976).sum := by decide
  have hdescent : baseEnd_3711976 < baseStart_3711976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711988 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3711988 : Nat := 118140960795 + 3711988 * 2 ^ 59
def prefixEnd_3711988 : Nat := 4983230072969 + 3 ^ 40 * 3711988 * 2
def baseEnd_3711988 : Nat := 1906034027721728063578885

theorem tailTrace_3711988 : CollatzResearch.WordTrace tailWord_3711988 prefixEnd_3711988 1906034027721728063578885 := by
  unfold tailWord_3711988
  simp only [CollatzResearch.WordTrace]
  refine ⟨67693662438054453961804309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90258216584072605282405745 67693662438054453961804309)
  ·
    refine ⟨3173140426783802529459577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67693662438054453961804309 3173140426783802529459577)
    ·
      refine ⟨2379855320087851897094683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3173140426783802529459577 2379855320087851897094683)
      ·
        refine ⟨3569782980131777845642025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379855320087851897094683 3569782980131777845642025)
        ·
          refine ⟨2677337235098833384231519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3569782980131777845642025 2677337235098833384231519)
          ·
            refine ⟨4016005852648250076347279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677337235098833384231519 4016005852648250076347279)
            ·
              refine ⟨6024008778972375114520919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016005852648250076347279 6024008778972375114520919)
              ·
                refine ⟨9036013168458562671781379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024008778972375114520919 9036013168458562671781379)
                ·
                  refine ⟨13554019752687844007672069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9036013168458562671781379 13554019752687844007672069)
                  ·
                    refine ⟨2541378703628970751438513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13554019752687844007672069 2541378703628970751438513)
                    ·
                      refine ⟨1906034027721728063578885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541378703628970751438513 1906034027721728063578885)
                      ·
                        rfl

theorem cell23_3711988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3711988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711988 prefixEnd_3711988 := by exact prefixLift 3711988
  have htrace : WordTrace (prefixWord ++ tailWord_3711988) baseStart_3711988 baseEnd_3711988 := by
    simpa [prefixWord, tailWord_3711988, baseEnd_3711988] using wordTrace_append hprefix tailTrace_3711988
  have hstable : (prefixWord ++ tailWord_3711988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711988).length < 2 ^ (prefixWord ++ tailWord_3711988).sum := by decide
  have hdescent : baseEnd_3711988 < baseStart_3711988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3711996 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_3711996 : Nat := 118140960795 + 3711996 * 2 ^ 59
def prefixEnd_3711996 : Nat := 4983230072969 + 3 ^ 40 * 3711996 * 2
def baseEnd_3711996 : Nat := 1906038135566964032278847

theorem tailTrace_3711996 : CollatzResearch.WordTrace tailWord_3711996 prefixEnd_3711996 1906038135566964032278847 := by
  unfold tailWord_3711996
  simp only [CollatzResearch.WordTrace]
  refine ⟨67693808330039962644949921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90258411106719950193266561 67693808330039962644949921)
  ·
    refine ⟨50770356247529971983712441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67693808330039962644949921 50770356247529971983712441)
    ·
      refine ⟨38077767185647478987784331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50770356247529971983712441 38077767185647478987784331)
      ·
        refine ⟨57116650778471218481676497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38077767185647478987784331 57116650778471218481676497)
        ·
          refine ⟨42837488083853413861257373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57116650778471218481676497 42837488083853413861257373)
          ·
            refine ⟨16064058031445030197971515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42837488083853413861257373 16064058031445030197971515)
            ·
              refine ⟨24096087047167545296957273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064058031445030197971515 24096087047167545296957273)
              ·
                refine ⟨18072065285375658972717955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24096087047167545296957273 18072065285375658972717955)
                ·
                  refine ⟨27108097928063488459076933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18072065285375658972717955 27108097928063488459076933)
                  ·
                    refine ⟨5082768361511904086076925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27108097928063488459076933 5082768361511904086076925)
                    ·
                      refine ⟨1906038135566964032278847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5082768361511904086076925 1906038135566964032278847)
                      ·
                        rfl

theorem cell23_3711996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_3711996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3711996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3711996 prefixEnd_3711996 := by exact prefixLift 3711996
  have htrace : WordTrace (prefixWord ++ tailWord_3711996) baseStart_3711996 baseEnd_3711996 := by
    simpa [prefixWord, tailWord_3711996, baseEnd_3711996] using wordTrace_append hprefix tailTrace_3711996
  have hstable : (prefixWord ++ tailWord_3711996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3711996).length < 2 ^ (prefixWord ++ tailWord_3711996).sum := by decide
  have hdescent : baseEnd_3711996 < baseStart_3711996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3711996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712053 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_3712053 : Nat := 118140960795 + 3712053 * 2 ^ 59
def prefixEnd_3712053 : Nat := 4983230072969 + 3 ^ 40 * 3712053 * 2
def baseEnd_3712053 : Nat := 1906067403964270309266085

theorem tailTrace_3712053 : CollatzResearch.WordTrace tailWord_3712053 prefixEnd_3712053 1906067403964270309266085 := by
  unfold tailWord_3712053
  simp only [CollatzResearch.WordTrace]
  refine ⟨135389695620873424024724813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90259797080582282683149875 135389695620873424024724813)
  ·
    refine ⟨50771135857827534009271805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135389695620873424024724813 50771135857827534009271805)
    ·
      refine ⟨19039175946685325253476927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50771135857827534009271805 19039175946685325253476927)
      ·
        refine ⟨28558763920027987880215391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19039175946685325253476927 28558763920027987880215391)
        ·
          refine ⟨42838145880041981820323087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28558763920027987880215391 42838145880041981820323087)
          ·
            refine ⟨64257218820062972730484631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42838145880041981820323087 64257218820062972730484631)
            ·
              refine ⟨96385828230094459095726947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64257218820062972730484631 96385828230094459095726947)
              ·
                refine ⟨144578742345141688643590421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96385828230094459095726947 144578742345141688643590421)
                ·
                  refine ⟨6777128547428516655168301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144578742345141688643590421 6777128547428516655168301)
                  ·
                    refine ⟨2541423205285693745688113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6777128547428516655168301 2541423205285693745688113)
                    ·
                      refine ⟨1906067403964270309266085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541423205285693745688113 1906067403964270309266085)
                      ·
                        rfl

theorem cell23_3712053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_3712053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712053 prefixEnd_3712053 := by exact prefixLift 3712053
  have htrace : WordTrace (prefixWord ++ tailWord_3712053) baseStart_3712053 baseEnd_3712053 := by
    simpa [prefixWord, tailWord_3712053, baseEnd_3712053] using wordTrace_append hprefix tailTrace_3712053
  have hstable : (prefixWord ++ tailWord_3712053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712053).length < 2 ^ (prefixWord ++ tailWord_3712053).sum := by decide
  have hdescent : baseEnd_3712053 < baseStart_3712053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712096 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_3712096 : Nat := 118140960795 + 3712096 * 2 ^ 59
def prefixEnd_3712096 : Nat := 4983230072969 + 3 ^ 40 * 3712096 * 2
def baseEnd_3712096 : Nat := 1906089483632413641028387

theorem tailTrace_3712096 : CollatzResearch.WordTrace tailWord_3712096 prefixEnd_3712096 1906089483632413641028387 := by
  unfold tailWord_3712096
  simp only [CollatzResearch.WordTrace]
  refine ⟨67695631979858821184270071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90260842639811761579026761 67695631979858821184270071)
  ·
    refine ⟨101543447969788231776405107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67695631979858821184270071 101543447969788231776405107)
    ·
      refine ⟨152315171954682347664607661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101543447969788231776405107 152315171954682347664607661)
      ·
        refine ⟨57118189483005880374227873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152315171954682347664607661 57118189483005880374227873)
        ·
          refine ⟨42838642112254410280670905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57118189483005880374227873 42838642112254410280670905)
          ·
            refine ⟨32128981584190807710503179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42838642112254410280670905 32128981584190807710503179)
            ·
              refine ⟨48193472376286211565754769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32128981584190807710503179 48193472376286211565754769)
              ·
                refine ⟨36145104282214658674316077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48193472376286211565754769 36145104282214658674316077)
                ·
                  refine ⟨13554414105830497002868529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36145104282214658674316077 13554414105830497002868529)
                  ·
                    refine ⟨10165810579372872752151397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13554414105830497002868529 10165810579372872752151397)
                    ·
                      refine ⟨1906089483632413641028387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10165810579372872752151397 1906089483632413641028387)
                      ·
                        rfl

theorem cell23_3712096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_3712096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712096 prefixEnd_3712096 := by exact prefixLift 3712096
  have htrace : WordTrace (prefixWord ++ tailWord_3712096) baseStart_3712096 baseEnd_3712096 := by
    simpa [prefixWord, tailWord_3712096, baseEnd_3712096] using wordTrace_append hprefix tailTrace_3712096
  have hstable : (prefixWord ++ tailWord_3712096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712096).length < 2 ^ (prefixWord ++ tailWord_3712096).sum := by decide
  have hdescent : baseEnd_3712096 < baseStart_3712096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712100 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_3712100 : Nat := 118140960795 + 3712100 * 2 ^ 59
def prefixEnd_3712100 : Nat := 4983230072969 + 3 ^ 40 * 3712100 * 2
def baseEnd_3712100 : Nat := 1906091537555031625378369

theorem tailTrace_3712100 : CollatzResearch.WordTrace tailWord_3712100 prefixEnd_3712100 1906091537555031625378369 := by
  unfold tailWord_3712100
  simp only [CollatzResearch.WordTrace]
  refine ⟨67695704925851575525842877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90260939901135434034457169 67695704925851575525842877)
  ·
    refine ⟨25385889347194340822191079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67695704925851575525842877 25385889347194340822191079)
    ·
      refine ⟨38078834020791511233286619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25385889347194340822191079 38078834020791511233286619)
      ·
        refine ⟨57118251031187266849929929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38078834020791511233286619 57118251031187266849929929)
        ·
          refine ⟨42838688273390450137447447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57118251031187266849929929 42838688273390450137447447)
          ·
            refine ⟨64258032410085675206171171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42838688273390450137447447 64258032410085675206171171)
            ·
              refine ⟨96387048615128512809256757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64258032410085675206171171 96387048615128512809256757)
              ·
                refine ⟨9036285807668298075867821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96387048615128512809256757 9036285807668298075867821)
                ·
                  refine ⟨3388607177875611778450433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9036285807668298075867821 3388607177875611778450433)
                  ·
                    refine ⟨2541455383406708833837825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3388607177875611778450433 2541455383406708833837825)
                    ·
                      refine ⟨1906091537555031625378369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541455383406708833837825 1906091537555031625378369)
                      ·
                        rfl

theorem cell23_3712100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_3712100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712100 prefixEnd_3712100 := by exact prefixLift 3712100
  have htrace : WordTrace (prefixWord ++ tailWord_3712100) baseStart_3712100 baseEnd_3712100 := by
    simpa [prefixWord, tailWord_3712100, baseEnd_3712100] using wordTrace_append hprefix tailTrace_3712100
  have hstable : (prefixWord ++ tailWord_3712100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712100).length < 2 ^ (prefixWord ++ tailWord_3712100).sum := by decide
  have hdescent : baseEnd_3712100 < baseStart_3712100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712103 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_3712103 : Nat := 118140960795 + 3712103 * 2 ^ 59
def prefixEnd_3712103 : Nat := 4983230072969 + 3 ^ 40 * 3712103 * 2
def baseEnd_3712103 : Nat := 1906093077996995113640855

theorem tailTrace_3712103 : CollatzResearch.WordTrace tailWord_3712103 prefixEnd_3712103 1906093077996995113640855 := by
  unfold tailWord_3712103
  simp only [CollatzResearch.WordTrace]
  refine ⟨135391519270692282564044963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90261012847128188376029975 135391519270692282564044963)
  ·
    refine ⟨203087278906038423846067445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135391519270692282564044963 203087278906038423846067445)
    ·
      refine ⟨19039432397441102235568823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203087278906038423846067445 19039432397441102235568823)
      ·
        refine ⟨28559148596161653353353235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19039432397441102235568823 28559148596161653353353235)
        ·
          refine ⟨42838722894242480030029853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28559148596161653353353235 42838722894242480030029853)
          ·
            refine ⟨16064521085340930011261195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42838722894242480030029853 16064521085340930011261195)
            ·
              refine ⟨24096781628011395016891793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064521085340930011261195 24096781628011395016891793)
              ·
                refine ⟨18072586221008546262668845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24096781628011395016891793 18072586221008546262668845)
                ·
                  refine ⟨6777219832878204848500817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18072586221008546262668845 6777219832878204848500817)
                  ·
                    refine ⟨5082914874658653636375613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777219832878204848500817 5082914874658653636375613)
                    ·
                      refine ⟨1906093077996995113640855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5082914874658653636375613 1906093077996995113640855)
                      ·
                        rfl

theorem cell23_3712103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_3712103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712103 prefixEnd_3712103 := by exact prefixLift 3712103
  have htrace : WordTrace (prefixWord ++ tailWord_3712103) baseStart_3712103 baseEnd_3712103 := by
    simpa [prefixWord, tailWord_3712103, baseEnd_3712103] using wordTrace_append hprefix tailTrace_3712103
  have hstable : (prefixWord ++ tailWord_3712103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712103).length < 2 ^ (prefixWord ++ tailWord_3712103).sum := by decide
  have hdescent : baseEnd_3712103 < baseStart_3712103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712110 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3712110 : Nat := 118140960795 + 3712110 * 2 ^ 59
def prefixEnd_3712110 : Nat := 4983230072969 + 3 ^ 40 * 3712110 * 2
def baseEnd_3712110 : Nat := 635365557453858862084441

theorem tailTrace_3712110 : CollatzResearch.WordTrace tailWord_3712110 prefixEnd_3712110 635365557453858862084441 := by
  unfold tailWord_3712110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923971822708365344943723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90261183054444615173033189 16923971822708365344943723)
  ·
    refine ⟨25385957734062548017415585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16923971822708365344943723 25385957734062548017415585)
    ·
      refine ⟨19039468300546911013061689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25385957734062548017415585 19039468300546911013061689)
      ·
        refine ⟨14279601225410183259796267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19039468300546911013061689 14279601225410183259796267)
        ·
          refine ⟨21419401838115274889694401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14279601225410183259796267 21419401838115274889694401)
          ·
            refine ⟨16064551378586456167270801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21419401838115274889694401 16064551378586456167270801)
            ·
              refine ⟨12048413533939842125453101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16064551378586456167270801 12048413533939842125453101)
              ·
                refine ⟨4518155075227440797044913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12048413533939842125453101 4518155075227440797044913)
                ·
                  refine ⟨3388616306420580597783685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4518155075227440797044913 3388616306420580597783685)
                  ·
                    refine ⟨635365557453858862084441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388616306420580597783685 635365557453858862084441)
                    ·
                      rfl

theorem cell23_3712110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3712110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712110 prefixEnd_3712110 := by exact prefixLift 3712110
  have htrace : WordTrace (prefixWord ++ tailWord_3712110) baseStart_3712110 baseEnd_3712110 := by
    simpa [prefixWord, tailWord_3712110, baseEnd_3712110] using wordTrace_append hprefix tailTrace_3712110
  have hstable : (prefixWord ++ tailWord_3712110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712110).length < 2 ^ (prefixWord ++ tailWord_3712110).sum := by decide
  have hdescent : baseEnd_3712110 < baseStart_3712110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712137 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 1, 2, 3]
def baseStart_3712137 : Nat := 118140960795 + 3712137 * 2 ^ 59
def prefixEnd_3712137 : Nat := 4983230072969 + 3 ^ 40 * 3712137 * 2
def baseEnd_3712137 : Nat := 1906110536339247980615699

theorem tailTrace_3712137 : CollatzResearch.WordTrace tailWord_3712137 prefixEnd_3712137 1906110536339247980615699 := by
  unfold tailWord_3712137
  simp only [CollatzResearch.WordTrace]
  refine ⟨135392759352569106370782665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90261839568379404247188443 135392759352569106370782665)
  ·
    refine ⟨101544569514426829778086999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135392759352569106370782665 101544569514426829778086999)
    ·
      refine ⟨152316854271640244667130499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101544569514426829778086999 152316854271640244667130499)
      ·
        refine ⟨228475281407460367000695749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152316854271640244667130499 228475281407460367000695749)
        ·
          refine ⟨42839115263898818812630453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228475281407460367000695749 42839115263898818812630453)
          ·
            refine ⟨4016167055990514263684105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42839115263898818812630453 4016167055990514263684105)
            ·
              refine ⟨3012125291992885697763079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4016167055990514263684105 3012125291992885697763079)
              ·
                refine ⟨4518187937989328546644619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012125291992885697763079 4518187937989328546644619)
                ·
                  refine ⟨6777281906983992819966929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518187937989328546644619 6777281906983992819966929)
                  ·
                    refine ⟨5082961430237994614975197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777281906983992819966929 5082961430237994614975197)
                    ·
                      refine ⟨1906110536339247980615699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5082961430237994614975197 1906110536339247980615699)
                      ·
                        rfl

theorem cell23_3712137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 2, 3].length) (baseStart_3712137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712137 prefixEnd_3712137 := by exact prefixLift 3712137
  have htrace : WordTrace (prefixWord ++ tailWord_3712137) baseStart_3712137 baseEnd_3712137 := by
    simpa [prefixWord, tailWord_3712137, baseEnd_3712137] using wordTrace_append hprefix tailTrace_3712137
  have hstable : (prefixWord ++ tailWord_3712137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712137).length < 2 ^ (prefixWord ++ tailWord_3712137).sum := by decide
  have hdescent : baseEnd_3712137 < baseStart_3712137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712167 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3712167 : Nat := 118140960795 + 3712167 * 2 ^ 59
def prefixEnd_3712167 : Nat := 4983230072969 + 3 ^ 40 * 3712167 * 2
def baseEnd_3712167 : Nat := 1906125940758882863240561

theorem tailTrace_3712167 : CollatzResearch.WordTrace tailWord_3712167 prefixEnd_3712167 1906125940758882863240561 := by
  unfold tailWord_3712167
  simp only [CollatzResearch.WordTrace]
  refine ⟨135393853542460421494374755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90262569028306947662916503 135393853542460421494374755)
  ·
    refine ⟨203090780313690632241562133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135393853542460421494374755 203090780313690632241562133)
    ·
      refine ⟨9519880327204248386323225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203090780313690632241562133 9519880327204248386323225)
      ·
        refine ⟨7139910245403186289742419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9519880327204248386323225 7139910245403186289742419)
        ·
          refine ⟨10709865368104779434613629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139910245403186289742419 10709865368104779434613629)
          ·
            refine ⟨4016199513039292287980111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10709865368104779434613629 4016199513039292287980111)
            ·
              refine ⟨6024299269558938431970167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016199513039292287980111 6024299269558938431970167)
              ·
                refine ⟨9036448904338407647955251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024299269558938431970167 9036448904338407647955251)
                ·
                  refine ⟨13554673356507611471932877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9036448904338407647955251 13554673356507611471932877)
                  ·
                    refine ⟨5083002508690354301974829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13554673356507611471932877 5083002508690354301974829)
                    ·
                      refine ⟨1906125940758882863240561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5083002508690354301974829 1906125940758882863240561)
                      ·
                        rfl

theorem cell23_3712167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3712167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712167 prefixEnd_3712167 := by exact prefixLift 3712167
  have htrace : WordTrace (prefixWord ++ tailWord_3712167) baseStart_3712167 baseEnd_3712167 := by
    simpa [prefixWord, tailWord_3712167, baseEnd_3712167] using wordTrace_append hprefix tailTrace_3712167
  have hstable : (prefixWord ++ tailWord_3712167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712167).length < 2 ^ (prefixWord ++ tailWord_3712167).sum := by decide
  have hdescent : baseEnd_3712167 < baseStart_3712167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712176 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_3712176 : Nat := 118140960795 + 3712176 * 2 ^ 59
def prefixEnd_3712176 : Nat := 4983230072969 + 3 ^ 40 * 3712176 * 2
def baseEnd_3712176 : Nat := 1906130562084773328028019

theorem tailTrace_3712176 : CollatzResearch.WordTrace tailWord_3712176 prefixEnd_3712176 1906130562084773328028019 := by
  unfold tailWord_3712176
  simp only [CollatzResearch.WordTrace]
  refine ⟨67697090899713908015726191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90262787866285210687634921 67697090899713908015726191)
  ·
    refine ⟨101545636349570862023589287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67697090899713908015726191 101545636349570862023589287)
    ·
      refine ⟨152318454524356293035383931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101545636349570862023589287 152318454524356293035383931)
      ·
        refine ⟨228477681786534439553075897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152318454524356293035383931 228477681786534439553075897)
        ·
          refine ⟨171358261339900829664806923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228477681786534439553075897 171358261339900829664806923)
          ·
            refine ⟨257037392009851244497210385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171358261339900829664806923 257037392009851244497210385)
            ·
              refine ⟨192778044007388433372907789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257037392009851244497210385 192778044007388433372907789)
              ·
                refine ⟨72291766502770662514840421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192778044007388433372907789 72291766502770662514840421)
                ·
                  refine ⟨13554706219269499221532579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72291766502770662514840421 13554706219269499221532579)
                  ·
                    refine ⟨20332059328904248832298869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13554706219269499221532579 20332059328904248832298869)
                    ·
                      refine ⟨1906130562084773328028019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20332059328904248832298869 1906130562084773328028019)
                      ·
                        rfl

theorem cell23_3712176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_3712176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712176 prefixEnd_3712176 := by exact prefixLift 3712176
  have htrace : WordTrace (prefixWord ++ tailWord_3712176) baseStart_3712176 baseEnd_3712176 := by
    simpa [prefixWord, tailWord_3712176, baseEnd_3712176] using wordTrace_append hprefix tailTrace_3712176
  have hstable : (prefixWord ++ tailWord_3712176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712176).length < 2 ^ (prefixWord ++ tailWord_3712176).sum := by decide
  have hdescent : baseEnd_3712176 < baseStart_3712176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712177 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3712177 : Nat := 118140960795 + 3712177 * 2 ^ 59
def prefixEnd_3712177 : Nat := 4983230072969 + 3 ^ 40 * 3712177 * 2
def baseEnd_3712177 : Nat := 1906131075565427824115515

theorem tailTrace_3712177 : CollatzResearch.WordTrace tailWord_3712177 prefixEnd_3712177 1906131075565427824115515 := by
  unfold tailWord_3712177
  simp only [CollatzResearch.WordTrace]
  refine ⟨135394218272424193202238785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90262812181616128801492523 135394218272424193202238785)
  ·
    refine ⟨101545663704318144901679089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135394218272424193202238785 101545663704318144901679089)
    ·
      refine ⟨76159247778238608676259317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101545663704318144901679089 76159247778238608676259317)
      ·
        refine ⟨7139929479209869563399311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76159247778238608676259317 7139929479209869563399311)
        ·
          refine ⟨10709894218814804345098967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139929479209869563399311 10709894218814804345098967)
          ·
            refine ⟨16064841328222206517648451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709894218814804345098967 16064841328222206517648451)
            ·
              refine ⟨24097261992333309776472677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064841328222206517648451 24097261992333309776472677)
              ·
                refine ⟨4518236623562495583088627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24097261992333309776472677 4518236623562495583088627)
                ·
                  refine ⟨6777354935343743374632941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518236623562495583088627 6777354935343743374632941)
                  ·
                    refine ⟨2541508100753903765487353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6777354935343743374632941 2541508100753903765487353)
                    ·
                      refine ⟨1906131075565427824115515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541508100753903765487353 1906131075565427824115515)
                      ·
                        rfl

theorem cell23_3712177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3712177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712177 prefixEnd_3712177 := by exact prefixLift 3712177
  have htrace : WordTrace (prefixWord ++ tailWord_3712177) baseStart_3712177 baseEnd_3712177 := by
    simpa [prefixWord, tailWord_3712177, baseEnd_3712177] using wordTrace_append hprefix tailTrace_3712177
  have hstable : (prefixWord ++ tailWord_3712177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712177).length < 2 ^ (prefixWord ++ tailWord_3712177).sum := by decide
  have hdescent : baseEnd_3712177 < baseStart_3712177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712223 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3]
def baseStart_3712223 : Nat := 118140960795 + 3712223 * 2 ^ 59
def prefixEnd_3712223 : Nat := 4983230072969 + 3 ^ 40 * 3712223 * 2
def baseEnd_3712223 : Nat := 1906154695675534644140303

theorem tailTrace_3712223 : CollatzResearch.WordTrace tailWord_3712223 prefixEnd_3712223 1906154695675534644140303 := by
  unfold tailWord_3712223
  simp only [CollatzResearch.WordTrace]
  refine ⟨135395896030257543058413323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90263930686838362038942215 135395896030257543058413323)
  ·
    refine ⟨203093844045386314587619985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135395896030257543058413323 203093844045386314587619985)
    ·
      refine ⟨152320383034039735940714989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203093844045386314587619985 152320383034039735940714989)
      ·
        refine ⟨57120143637764900977768121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152320383034039735940714989 57120143637764900977768121)
        ·
          refine ⟨42840107728323675733326091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57120143637764900977768121 42840107728323675733326091)
          ·
            refine ⟨64260161592485513599989137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42840107728323675733326091 64260161592485513599989137)
            ·
              refine ⟨48195121194364135199991853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64260161592485513599989137 48195121194364135199991853)
              ·
                refine ⟨18073170447886550699996945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48195121194364135199991853 18073170447886550699996945)
                ·
                  refine ⟨13554877835914913024997709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18073170447886550699996945 13554877835914913024997709)
                  ·
                    refine ⟨5083079188468092384374141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13554877835914913024997709 5083079188468092384374141)
                    ·
                      refine ⟨1906154695675534644140303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5083079188468092384374141 1906154695675534644140303)
                      ·
                        rfl

theorem cell23_3712223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_3712223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712223 prefixEnd_3712223 := by exact prefixLift 3712223
  have htrace : WordTrace (prefixWord ++ tailWord_3712223) baseStart_3712223 baseEnd_3712223 := by
    simpa [prefixWord, tailWord_3712223, baseEnd_3712223] using wordTrace_append hprefix tailTrace_3712223
  have hstable : (prefixWord ++ tailWord_3712223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712223).length < 2 ^ (prefixWord ++ tailWord_3712223).sum := by decide
  have hdescent : baseEnd_3712223 < baseStart_3712223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712224 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 2, 2, 2]
def baseStart_3712224 : Nat := 118140960795 + 3712224 * 2 ^ 59
def prefixEnd_3712224 : Nat := 4983230072969 + 3 ^ 40 * 3712224 * 2
def baseEnd_3712224 : Nat := 1906155209156189140227799

theorem tailTrace_3712224 : CollatzResearch.WordTrace tailWord_3712224 prefixEnd_3712224 1906155209156189140227799 := by
  unfold tailWord_3712224
  simp only [CollatzResearch.WordTrace]
  refine ⟨67697966251626960114599863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90263955002169280152799817 67697966251626960114599863)
  ·
    refine ⟨101546949377440440171899795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67697966251626960114599863 101546949377440440171899795)
    ·
      refine ⟨152320424066160660257849693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101546949377440440171899795 152320424066160660257849693)
      ·
        refine ⟨57120159024810247596693635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152320424066160660257849693 57120159024810247596693635)
        ·
          refine ⟨85680238537215371395040453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57120159024810247596693635 85680238537215371395040453)
          ·
            refine ⟨16065044725727882136570085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85680238537215371395040453 16065044725727882136570085)
            ·
              refine ⟨3012195886073977900606891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16065044725727882136570085 3012195886073977900606891)
              ·
                refine ⟨4518293829110966850910337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012195886073977900606891 4518293829110966850910337)
                ·
                  refine ⟨3388720371833225138182753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4518293829110966850910337 3388720371833225138182753)
                  ·
                    refine ⟨2541540278874918853637065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3388720371833225138182753 2541540278874918853637065)
                    ·
                      refine ⟨1906155209156189140227799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541540278874918853637065 1906155209156189140227799)
                      ·
                        rfl

theorem cell23_3712224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_3712224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712224 prefixEnd_3712224 := by exact prefixLift 3712224
  have htrace : WordTrace (prefixWord ++ tailWord_3712224) baseStart_3712224 baseEnd_3712224 := by
    simpa [prefixWord, tailWord_3712224, baseEnd_3712224] using wordTrace_append hprefix tailTrace_3712224
  have hstable : (prefixWord ++ tailWord_3712224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712224).length < 2 ^ (prefixWord ++ tailWord_3712224).sum := by decide
  have hdescent : baseEnd_3712224 < baseStart_3712224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712243 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 2, 5]
def baseStart_3712243 : Nat := 118140960795 + 3712243 * 2 ^ 59
def prefixEnd_3712243 : Nat := 4983230072969 + 3 ^ 40 * 3712243 * 2
def baseEnd_3712243 : Nat := 635388321762874855296737

theorem tailTrace_3712243 : CollatzResearch.WordTrace tailWord_3712243 prefixEnd_3712243 635388321762874855296737 := by
  unfold tailWord_3712243
  simp only [CollatzResearch.WordTrace]
  refine ⟨135396625490185086474141383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90264416993456724316094255 135396625490185086474141383)
  ·
    refine ⟨203094938235277629711212075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135396625490185086474141383 203094938235277629711212075)
    ·
      refine ⟨304642407352916444566818113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203094938235277629711212075 304642407352916444566818113)
      ·
        refine ⟨228481805514687333425113585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304642407352916444566818113 228481805514687333425113585)
        ·
          refine ⟨171361354136015500068835189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228481805514687333425113585 171361354136015500068835189)
          ·
            refine ⟨16065126950251453131453299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171361354136015500068835189 16065126950251453131453299)
            ·
              refine ⟨24097690425377179697179949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16065126950251453131453299 24097690425377179697179949)
              ·
                refine ⟨9036633909516442386442481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24097690425377179697179949 9036633909516442386442481)
                ·
                  refine ⟨6777475432137331789831861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9036633909516442386442481 6777475432137331789831861)
                  ·
                    refine ⟨635388321762874855296737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6777475432137331789831861 635388321762874855296737)
                    ·
                      rfl

theorem cell23_3712243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 5].length) (baseStart_3712243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712243 prefixEnd_3712243 := by exact prefixLift 3712243
  have htrace : WordTrace (prefixWord ++ tailWord_3712243) baseStart_3712243 baseEnd_3712243 := by
    simpa [prefixWord, tailWord_3712243, baseEnd_3712243] using wordTrace_append hprefix tailTrace_3712243
  have hstable : (prefixWord ++ tailWord_3712243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712243).length < 2 ^ (prefixWord ++ tailWord_3712243).sum := by decide
  have hdescent : baseEnd_3712243 < baseStart_3712243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712260 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_3712260 : Nat := 118140960795 + 3712260 * 2 ^ 59
def prefixEnd_3712260 : Nat := 4983230072969 + 3 ^ 40 * 3712260 * 2
def baseEnd_3712260 : Nat := 635391231486583666459211

theorem tailTrace_3712260 : CollatzResearch.WordTrace tailWord_3712260 prefixEnd_3712260 635391231486583666459211 := by
  unfold tailWord_3712260
  simp only [CollatzResearch.WordTrace]
  refine ⟨67698622765561749188755117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90264830354082332251673489 67698622765561749188755117)
  ·
    refine ⟨25386983537085655945783169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67698622765561749188755117 25386983537085655945783169)
    ·
      refine ⟨19040237652814241959337377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25386983537085655945783169 19040237652814241959337377)
      ·
        refine ⟨14280178239610681469503033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19040237652814241959337377 14280178239610681469503033)
        ·
          refine ⟨10710133679708011102127275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14280178239610681469503033 10710133679708011102127275)
          ·
            refine ⟨16065200519562016653190913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10710133679708011102127275 16065200519562016653190913)
            ·
              refine ⟨12048900389671512489893185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16065200519562016653190913 12048900389671512489893185)
              ·
                refine ⟨9036675292253634367419889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12048900389671512489893185 9036675292253634367419889)
                ·
                  refine ⟨6777506469190225775564917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9036675292253634367419889 6777506469190225775564917)
                  ·
                    refine ⟨635391231486583666459211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6777506469190225775564917 635391231486583666459211)
                    ·
                      rfl

theorem cell23_3712260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_3712260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712260 prefixEnd_3712260 := by exact prefixLift 3712260
  have htrace : WordTrace (prefixWord ++ tailWord_3712260) baseStart_3712260 baseEnd_3712260 := by
    simpa [prefixWord, tailWord_3712260, baseEnd_3712260] using wordTrace_append hprefix tailTrace_3712260
  have hstable : (prefixWord ++ tailWord_3712260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712260).length < 2 ^ (prefixWord ++ tailWord_3712260).sum := by decide
  have hdescent : baseEnd_3712260 < baseStart_3712260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712264 : List Nat := [2, 1, 3, 2, 4, 2, 2, 2, 5]
def baseStart_3712264 : Nat := 118140960795 + 3712264 * 2 ^ 59
def prefixEnd_3712264 : Nat := 4983230072969 + 3 ^ 40 * 3712264 * 2
def baseEnd_3712264 : Nat := 211797305375818775969735

theorem tailTrace_3712264 : CollatzResearch.WordTrace tailWord_3712264 prefixEnd_3712264 211797305375818775969735 := by
  unfold tailWord_3712264
  simp only [CollatzResearch.WordTrace]
  refine ⟨67698695711554503530327923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90264927615406004707103897 67698695711554503530327923)
  ·
    refine ⟨101548043567331755295491885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67698695711554503530327923 101548043567331755295491885)
    ·
      refine ⟨38080516337749408235809457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101548043567331755295491885 38080516337749408235809457)
      ·
        refine ⟨28560387253312056176857093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38080516337749408235809457 28560387253312056176857093)
        ·
          refine ⟨5355072609996010533160705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28560387253312056176857093 5355072609996010533160705)
          ·
            refine ⟨4016304457497007899870529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5355072609996010533160705 4016304457497007899870529)
            ·
              refine ⟨3012228343122755924902897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4016304457497007899870529 3012228343122755924902897)
              ·
                refine ⟨2259171257342066943677173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012228343122755924902897 2259171257342066943677173)
                ·
                  refine ⟨211797305375818775969735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2259171257342066943677173 211797305375818775969735)
                  ·
                    rfl

theorem cell23_3712264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 5].length) (baseStart_3712264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712264 prefixEnd_3712264 := by exact prefixLift 3712264
  have htrace : WordTrace (prefixWord ++ tailWord_3712264) baseStart_3712264 baseEnd_3712264 := by
    simpa [prefixWord, tailWord_3712264, baseEnd_3712264] using wordTrace_append hprefix tailTrace_3712264
  have hstable : (prefixWord ++ tailWord_3712264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712264).length < 2 ^ (prefixWord ++ tailWord_3712264).sum := by decide
  have hdescent : baseEnd_3712264 < baseStart_3712264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712274 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3712274 : Nat := 118140960795 + 3712274 * 2 ^ 59
def prefixEnd_3712274 : Nat := 4983230072969 + 3 ^ 40 * 3712274 * 2
def baseEnd_3712274 : Nat := 1906180883188913944602569

theorem tailTrace_3712274 : CollatzResearch.WordTrace tailWord_3712274 prefixEnd_3712274 1906180883188913944602569 := by
  unfold tailWord_3712274
  simp only [CollatzResearch.WordTrace]
  refine ⟨33849439038268194692129969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90265170768715185845679917 33849439038268194692129969)
  ·
    refine ⟨25387079278701146019097477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33849439038268194692129969 25387079278701146019097477)
    ·
      refine ⟨4760077364756464878580777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25387079278701146019097477 4760077364756464878580777)
      ·
        refine ⟨3570058023567348658935583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4760077364756464878580777 3570058023567348658935583)
        ·
          refine ⟨5355087035351022988403375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570058023567348658935583 5355087035351022988403375)
          ·
            refine ⟨8032630553026534482605063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355087035351022988403375 8032630553026534482605063)
            ·
              refine ⟨12048945829539801723907595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8032630553026534482605063 12048945829539801723907595)
              ·
                refine ⟨18073418744309702585861393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12048945829539801723907595 18073418744309702585861393)
                ·
                  refine ⟨13555064058232276939396045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18073418744309702585861393 13555064058232276939396045)
                  ·
                    refine ⟨5083149021837103852273517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13555064058232276939396045 5083149021837103852273517)
                    ·
                      refine ⟨1906180883188913944602569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5083149021837103852273517 1906180883188913944602569)
                      ·
                        rfl

theorem cell23_3712274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3712274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712274 prefixEnd_3712274 := by exact prefixLift 3712274
  have htrace : WordTrace (prefixWord ++ tailWord_3712274) baseStart_3712274 baseEnd_3712274 := by
    simpa [prefixWord, tailWord_3712274, baseEnd_3712274] using wordTrace_append hprefix tailTrace_3712274
  have hstable : (prefixWord ++ tailWord_3712274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712274).length < 2 ^ (prefixWord ++ tailWord_3712274).sum := by decide
  have hdescent : baseEnd_3712274 < baseStart_3712274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712280 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 1, 6, 2]
def baseStart_3712280 : Nat := 118140960795 + 3712280 * 2 ^ 59
def prefixEnd_3712280 : Nat := 4983230072969 + 3 ^ 40 * 3712280 * 2
def baseEnd_3712280 : Nat := 1906183964072840921127541

theorem tailTrace_3712280 : CollatzResearch.WordTrace tailWord_3712280 prefixEnd_3712280 1906183964072840921127541 := by
  unfold tailWord_3712280
  simp only [CollatzResearch.WordTrace]
  refine ⟨67698987495525520896619147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90265316660700694528825529 67698987495525520896619147)
  ·
    refine ⟨101548481243288281344928721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67698987495525520896619147 101548481243288281344928721)
    ·
      refine ⟨76161360932466211008696541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101548481243288281344928721 76161360932466211008696541)
      ·
        refine ⟨28560510349674829128261203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76161360932466211008696541 28560510349674829128261203)
        ·
          refine ⟨42840765524512243692391805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28560510349674829128261203 42840765524512243692391805)
          ·
            refine ⟨16065287071692091384646927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42840765524512243692391805 16065287071692091384646927)
            ·
              refine ⟨24097930607538137076970391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16065287071692091384646927 24097930607538137076970391)
              ·
                refine ⟨36146895911307205615455587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24097930607538137076970391 36146895911307205615455587)
                ·
                  refine ⟨54220343866960808423183381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36146895911307205615455587 54220343866960808423183381)
                  ·
                    refine ⟨2541578618763787894836721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54220343866960808423183381 2541578618763787894836721)
                    ·
                      refine ⟨1906183964072840921127541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541578618763787894836721 1906183964072840921127541)
                      ·
                        rfl

theorem cell23_3712280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_3712280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712280 prefixEnd_3712280 := by exact prefixLift 3712280
  have htrace : WordTrace (prefixWord ++ tailWord_3712280) baseStart_3712280 baseEnd_3712280 := by
    simpa [prefixWord, tailWord_3712280, baseEnd_3712280] using wordTrace_append hprefix tailTrace_3712280
  have hstable : (prefixWord ++ tailWord_3712280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712280).length < 2 ^ (prefixWord ++ tailWord_3712280).sum := by decide
  have hdescent : baseEnd_3712280 < baseStart_3712280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712283 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 3]
def baseStart_3712283 : Nat := 118140960795 + 3712283 * 2 ^ 59
def prefixEnd_3712283 : Nat := 4983230072969 + 3 ^ 40 * 3712283 * 2
def baseEnd_3712283 : Nat := 1906185504514804409390027

theorem tailTrace_3712283 : CollatzResearch.WordTrace tailWord_3712283 prefixEnd_3712283 1906185504514804409390027 := by
  unfold tailWord_3712283
  simp only [CollatzResearch.WordTrace]
  refine ⟨135398084410040173305597503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90265389606693448870398335 135398084410040173305597503)
  ·
    refine ⟨203097126615060259958396255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135398084410040173305597503 203097126615060259958396255)
    ·
      refine ⟨304645689922590389937594383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203097126615060259958396255 304645689922590389937594383)
      ·
        refine ⟨456968534883885584906391575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304645689922590389937594383 456968534883885584906391575)
        ·
          refine ⟨685452802325828377359587363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456968534883885584906391575 685452802325828377359587363)
          ·
            refine ⟨1028179203488742566039381045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685452802325828377359587363 1028179203488742566039381045)
            ·
              refine ⟨96391800327069615566191973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1028179203488742566039381045 96391800327069615566191973)
              ·
                refine ⟨18073462561325552918660995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96391800327069615566191973 18073462561325552918660995)
                ·
                  refine ⟨27110193841988329377991493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18073462561325552918660995 27110193841988329377991493)
                  ·
                    refine ⟨5083161345372811758373405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27110193841988329377991493 5083161345372811758373405)
                    ·
                      refine ⟨1906185504514804409390027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5083161345372811758373405 1906185504514804409390027)
                      ·
                        rfl

theorem cell23_3712283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 3].length) (baseStart_3712283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712283 prefixEnd_3712283 := by exact prefixLift 3712283
  have htrace : WordTrace (prefixWord ++ tailWord_3712283) baseStart_3712283 baseEnd_3712283 := by
    simpa [prefixWord, tailWord_3712283, baseEnd_3712283] using wordTrace_append hprefix tailTrace_3712283
  have hstable : (prefixWord ++ tailWord_3712283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712283).length < 2 ^ (prefixWord ++ tailWord_3712283).sum := by decide
  have hdescent : baseEnd_3712283 < baseStart_3712283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712307 : List Nat := [1, 1, 1, 2, 5, 2, 1, 5, 1, 4]
def baseStart_3712307 : Nat := 118140960795 + 3712307 * 2 ^ 59
def prefixEnd_3712307 : Nat := 4983230072969 + 3 ^ 40 * 3712307 * 2
def baseEnd_3712307 : Nat := 635399276016837438496639

theorem tailTrace_3712307 : CollatzResearch.WordTrace tailWord_3712307 prefixEnd_3712307 635399276016837438496639 := by
  unfold tailWord_3712307
  simp only [CollatzResearch.WordTrace]
  refine ⟨135398959761953225404471175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90265973174635483602980783 135398959761953225404471175)
  ·
    refine ⟨203098439642929838106706763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135398959761953225404471175 203098439642929838106706763)
    ·
      refine ⟨304647659464394757160060145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203098439642929838106706763 304647659464394757160060145)
      ·
        refine ⟨228485744598296067870045109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304647659464394757160060145 228485744598296067870045109)
        ·
          refine ⟨21420538556090256362816729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228485744598296067870045109 21420538556090256362816729)
          ·
            refine ⟨16065403917067692272112547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21420538556090256362816729 16065403917067692272112547)
            ·
              refine ⟨24098105875601538408168821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16065403917067692272112547 24098105875601538408168821)
              ·
                refine ⟨2259197425837644225765827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24098105875601538408168821 2259197425837644225765827)
                ·
                  refine ⟨3388796138756466338648741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259197425837644225765827 3388796138756466338648741)
                  ·
                    refine ⟨635399276016837438496639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388796138756466338648741 635399276016837438496639)
                    ·
                      rfl

theorem cell23_3712307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 4].length) (baseStart_3712307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712307 prefixEnd_3712307 := by exact prefixLift 3712307
  have htrace : WordTrace (prefixWord ++ tailWord_3712307) baseStart_3712307 baseEnd_3712307 := by
    simpa [prefixWord, tailWord_3712307, baseEnd_3712307] using wordTrace_append hprefix tailTrace_3712307
  have hstable : (prefixWord ++ tailWord_3712307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712307).length < 2 ^ (prefixWord ++ tailWord_3712307).sum := by decide
  have hdescent : baseEnd_3712307 < baseStart_3712307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712324 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3712324 : Nat := 118140960795 + 3712324 * 2 ^ 59
def prefixEnd_3712324 : Nat := 4983230072969 + 3 ^ 40 * 3712324 * 2
def baseEnd_3712324 : Nat := 635402185740546249659113

theorem tailTrace_3712324 : CollatzResearch.WordTrace tailWord_3712324 prefixEnd_3712324 635402185740546249659113 := by
  unfold tailWord_3712324
  simp only [CollatzResearch.WordTrace]
  refine ⟨67699789901445818653920013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90266386535261091538560017 67699789901445818653920013)
  ·
    refine ⟨25387421213042181995220005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67699789901445818653920013 25387421213042181995220005)
    ·
      refine ⟨4760141477445409124103751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25387421213042181995220005 4760141477445409124103751)
      ·
        refine ⟨7140212216168113686155627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760141477445409124103751 7140212216168113686155627)
        ·
          refine ⟨10710318324252170529233441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7140212216168113686155627 10710318324252170529233441)
          ·
            refine ⟨8032738743189127896925081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10710318324252170529233441 8032738743189127896925081)
            ·
              refine ⟨6024554057391845922693811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8032738743189127896925081 6024554057391845922693811)
              ·
                refine ⟨9036831086087768884040717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024554057391845922693811 9036831086087768884040717)
                ·
                  refine ⟨3388811657282913331515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9036831086087768884040717 3388811657282913331515269)
                  ·
                    refine ⟨635402185740546249659113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388811657282913331515269 635402185740546249659113)
                    ·
                      rfl

theorem cell23_3712324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3712324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712324 prefixEnd_3712324 := by exact prefixLift 3712324
  have htrace : WordTrace (prefixWord ++ tailWord_3712324) baseStart_3712324 baseEnd_3712324 := by
    simpa [prefixWord, tailWord_3712324, baseEnd_3712324] using wordTrace_append hprefix tailTrace_3712324
  have hstable : (prefixWord ++ tailWord_3712324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712324).length < 2 ^ (prefixWord ++ tailWord_3712324).sum := by decide
  have hdescent : baseEnd_3712324 < baseStart_3712324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712353 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3712353 : Nat := 118140960795 + 3712353 * 2 ^ 59
def prefixEnd_3712353 : Nat := 4983230072969 + 3 ^ 40 * 3712353 * 2
def baseEnd_3712353 : Nat := 1906221448160619135514705

theorem tailTrace_3712353 : CollatzResearch.WordTrace tailWord_3712353 prefixEnd_3712353 1906221448160619135514705 := by
  unfold tailWord_3712353
  simp only [CollatzResearch.WordTrace]
  refine ⟨135400637519786575260645713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90267091679857716840430475 135400637519786575260645713)
  ·
    refine ⟨101550478139839931445484285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135400637519786575260645713 101550478139839931445484285)
    ·
      refine ⟨38081429302439974292056607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101550478139839931445484285 38081429302439974292056607)
      ·
        refine ⟨57122143953659961438084911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38081429302439974292056607 57122143953659961438084911)
        ·
          refine ⟨85683215930489942157127367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57122143953659961438084911 85683215930489942157127367)
          ·
            refine ⟨128524823895734913235691051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85683215930489942157127367 128524823895734913235691051)
            ·
              refine ⟨192787235843602369853536577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128524823895734913235691051 192787235843602369853536577)
              ·
                refine ⟨144590426882701777390152433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192787235843602369853536577 144590426882701777390152433)
                ·
                  refine ⟨108442820162026333042614325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144590426882701777390152433 108442820162026333042614325)
                  ·
                    refine ⟨10166514390189968722745093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108442820162026333042614325 10166514390189968722745093)
                    ·
                      refine ⟨1906221448160619135514705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10166514390189968722745093 1906221448160619135514705)
                      ·
                        rfl

theorem cell23_3712353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3712353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712353 prefixEnd_3712353 := by exact prefixLift 3712353
  have htrace : WordTrace (prefixWord ++ tailWord_3712353) baseStart_3712353 baseEnd_3712353 := by
    simpa [prefixWord, tailWord_3712353, baseEnd_3712353] using wordTrace_append hprefix tailTrace_3712353
  have hstable : (prefixWord ++ tailWord_3712353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712353).length < 2 ^ (prefixWord ++ tailWord_3712353).sum := by decide
  have hdescent : baseEnd_3712353 < baseStart_3712353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712357 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 2, 3, 2]
def baseStart_3712357 : Nat := 118140960795 + 3712357 * 2 ^ 59
def prefixEnd_3712357 : Nat := 4983230072969 + 3 ^ 40 * 3712357 * 2
def baseEnd_3712357 : Nat := 1906223502083237119864687

theorem tailTrace_3712357 : CollatzResearch.WordTrace tailWord_3712357 prefixEnd_3712357 1906223502083237119864687 := by
  unfold tailWord_3712357
  simp only [CollatzResearch.WordTrace]
  refine ⟨135400783411772083943791325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90267188941181389295860883 135400783411772083943791325)
  ·
    refine ⟨50775293779414531478921747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135400783411772083943791325 50775293779414531478921747)
    ·
      refine ⟨76162940669121797218382621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50775293779414531478921747 76162940669121797218382621)
      ·
        refine ⟨28561102750920673956893483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76162940669121797218382621 28561102750920673956893483)
        ·
          refine ⟨42841654126381010935340225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28561102750920673956893483 42841654126381010935340225)
          ·
            refine ⟨32131240594785758201505169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42841654126381010935340225 32131240594785758201505169)
            ·
              refine ⟨24098430446089318651128877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32131240594785758201505169 24098430446089318651128877)
              ·
                refine ⟨9036911417283494494173329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24098430446089318651128877 9036911417283494494173329)
                ·
                  refine ⟨6777683562962620870629997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9036911417283494494173329 6777683562962620870629997)
                  ·
                    refine ⟨2541631336110982826486249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6777683562962620870629997 2541631336110982826486249)
                    ·
                      refine ⟨1906223502083237119864687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541631336110982826486249 1906223502083237119864687)
                      ·
                        rfl

theorem cell23_3712357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_3712357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712357 prefixEnd_3712357 := by exact prefixLift 3712357
  have htrace : WordTrace (prefixWord ++ tailWord_3712357) baseStart_3712357 baseEnd_3712357 := by
    simpa [prefixWord, tailWord_3712357, baseEnd_3712357] using wordTrace_append hprefix tailTrace_3712357
  have hstable : (prefixWord ++ tailWord_3712357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712357).length < 2 ^ (prefixWord ++ tailWord_3712357).sum := by decide
  have hdescent : baseEnd_3712357 < baseStart_3712357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712380 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_3712380 : Nat := 118140960795 + 3712380 * 2 ^ 59
def prefixEnd_3712380 : Nat := 4983230072969 + 3 ^ 40 * 3712380 * 2
def baseEnd_3712380 : Nat := 635411770712763509959027

theorem tailTrace_3712380 : CollatzResearch.WordTrace tailWord_3712380 prefixEnd_3712380 635411770712763509959027 := by
  unfold tailWord_3712380
  simp only [CollatzResearch.WordTrace]
  refine ⟨67700811145344379435939297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90267748193792505914585729 67700811145344379435939297)
  ·
    refine ⟨50775608359008284576954473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67700811145344379435939297 50775608359008284576954473)
    ·
      refine ⟨38081706269256213432715855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50775608359008284576954473 38081706269256213432715855)
      ·
        refine ⟨57122559403884320149073783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38081706269256213432715855 57122559403884320149073783)
        ·
          refine ⟨85683839105826480223610675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57122559403884320149073783 85683839105826480223610675)
          ·
            refine ⟨128525758658739720335416013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85683839105826480223610675 128525758658739720335416013)
            ·
              refine ⟨48197159497027395125781005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128525758658739720335416013 48197159497027395125781005)
              ·
                refine ⟨18073934811385273172167877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48197159497027395125781005 18073934811385273172167877)
                ·
                  refine ⟨3388862777134738719781477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18073934811385273172167877 3388862777134738719781477)
                  ·
                    refine ⟨635411770712763509959027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388862777134738719781477 635411770712763509959027)
                    ·
                      rfl

theorem cell23_3712380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_3712380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712380 prefixEnd_3712380 := by exact prefixLift 3712380
  have htrace : WordTrace (prefixWord ++ tailWord_3712380) baseStart_3712380 baseEnd_3712380 := by
    simpa [prefixWord, tailWord_3712380, baseEnd_3712380] using wordTrace_append hprefix tailTrace_3712380
  have hstable : (prefixWord ++ tailWord_3712380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712380).length < 2 ^ (prefixWord ++ tailWord_3712380).sum := by decide
  have hdescent : baseEnd_3712380 < baseStart_3712380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712381 : List Nat := [1, 4, 1, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_3712381 : Nat := 118140960795 + 3712381 * 2 ^ 59
def prefixEnd_3712381 : Nat := 4983230072969 + 3 ^ 40 * 3712381 * 2
def baseEnd_3712381 : Nat := 1906235825618945025964577

theorem tailTrace_3712381 : CollatzResearch.WordTrace tailWord_3712381 prefixEnd_3712381 1906235825618945025964577 := by
  unfold tailWord_3712381
  simp only [CollatzResearch.WordTrace]
  refine ⟨135401658763685136042664997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90267772509123424028443331 135401658763685136042664997)
  ·
    refine ⟨25387811018190963007999687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135401658763685136042664997 25387811018190963007999687)
    ·
      refine ⟨38081716527286444511999531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25387811018190963007999687 38081716527286444511999531)
      ·
        refine ⟨57122574790929666767999297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38081716527286444511999531 57122574790929666767999297)
        ·
          refine ⟨42841931093197250075999473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57122574790929666767999297 42841931093197250075999473)
          ·
            refine ⟨32131448319897937556999605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42841931093197250075999473 32131448319897937556999605)
            ·
              refine ⟨3012323279990431645968713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32131448319897937556999605 3012323279990431645968713)
              ·
                refine ⟨2259242459992823734476535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012323279990431645968713 2259242459992823734476535)
                ·
                  refine ⟨3388863689989235601714803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259242459992823734476535 3388863689989235601714803)
                  ·
                    refine ⟨5083295534983853402572205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3388863689989235601714803 5083295534983853402572205)
                    ·
                      refine ⟨1906235825618945025964577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5083295534983853402572205 1906235825618945025964577)
                      ·
                        rfl

theorem cell23_3712381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_3712381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712381 prefixEnd_3712381 := by exact prefixLift 3712381
  have htrace : WordTrace (prefixWord ++ tailWord_3712381) baseStart_3712381 baseEnd_3712381 := by
    simpa [prefixWord, tailWord_3712381, baseEnd_3712381] using wordTrace_append hprefix tailTrace_3712381
  have hstable : (prefixWord ++ tailWord_3712381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712381).length < 2 ^ (prefixWord ++ tailWord_3712381).sum := by decide
  have hdescent : baseEnd_3712381 < baseStart_3712381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712383 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_3712383 : Nat := 118140960795 + 3712383 * 2 ^ 59
def prefixEnd_3712383 : Nat := 4983230072969 + 3 ^ 40 * 3712383 * 2
def baseEnd_3712383 : Nat := 1906236852580254018139567

theorem tailTrace_3712383 : CollatzResearch.WordTrace tailWord_3712383 prefixEnd_3712383 1906236852580254018139567 := by
  unfold tailWord_3712383
  simp only [CollatzResearch.WordTrace]
  refine ⟨135401731709677890384237803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90267821139785260256158535 135401731709677890384237803)
  ·
    refine ⟨203102597564516835576356705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135401731709677890384237803 203102597564516835576356705)
    ·
      refine ⟨152326948173387626682267529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203102597564516835576356705 152326948173387626682267529)
      ·
        refine ⟨114245211130040720011700647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152326948173387626682267529 114245211130040720011700647)
        ·
          refine ⟨171367816695061080017550971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114245211130040720011700647 171367816695061080017550971)
          ·
            refine ⟨257051725042591620026326457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171367816695061080017550971 257051725042591620026326457)
            ·
              refine ⟨192788793781943715019744843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257051725042591620026326457 192788793781943715019744843)
              ·
                refine ⟨289183190672915572529617265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192788793781943715019744843 289183190672915572529617265)
                ·
                  refine ⟨216887393004686679397212949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289183190672915572529617265 216887393004686679397212949)
                  ·
                    refine ⟨10166596547094688096744357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 216887393004686679397212949 10166596547094688096744357)
                    ·
                      refine ⟨1906236852580254018139567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10166596547094688096744357 1906236852580254018139567)
                      ·
                        rfl

theorem cell23_3712383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_3712383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712383 prefixEnd_3712383 := by exact prefixLift 3712383
  have htrace : WordTrace (prefixWord ++ tailWord_3712383) baseStart_3712383 baseEnd_3712383 := by
    simpa [prefixWord, tailWord_3712383, baseEnd_3712383] using wordTrace_append hprefix tailTrace_3712383
  have hstable : (prefixWord ++ tailWord_3712383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712383).length < 2 ^ (prefixWord ++ tailWord_3712383).sum := by decide
  have hdescent : baseEnd_3712383 < baseStart_3712383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712404 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3712404 : Nat := 118140960795 + 3712404 * 2 ^ 59
def prefixEnd_3712404 : Nat := 4983230072969 + 3 ^ 40 * 3712404 * 2
def baseEnd_3712404 : Nat := 1906247635673998435976971

theorem tailTrace_3712404 : CollatzResearch.WordTrace tailWord_3712404 prefixEnd_3712404 1906247635673998435976971 := by
  unfold tailWord_3712404
  simp only [CollatzResearch.WordTrace]
  refine ⟨67701248821300905485376133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90268331761734540647168177 67701248821300905485376133)
  ·
    refine ⟨12693984153993919778508025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67701248821300905485376133 12693984153993919778508025)
    ·
      refine ⟨9520488115495439833881019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12693984153993919778508025 9520488115495439833881019)
      ·
        refine ⟨14280732173243159750821529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9520488115495439833881019 14280732173243159750821529)
        ·
          refine ⟨10710549129932369813116147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14280732173243159750821529 10710549129932369813116147)
          ·
            refine ⟨16065823694898554719674221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10710549129932369813116147 16065823694898554719674221)
            ·
              refine ⟨6024683885586958019877833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16065823694898554719674221 6024683885586958019877833)
              ·
                refine ⟨4518512914190218514908375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6024683885586958019877833 4518512914190218514908375)
                ·
                  refine ⟨6777769371285327772362563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518512914190218514908375 6777769371285327772362563)
                  ·
                    refine ⟨10166654056927991658543845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6777769371285327772362563 10166654056927991658543845)
                    ·
                      refine ⟨1906247635673998435976971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10166654056927991658543845 1906247635673998435976971)
                      ·
                        rfl

theorem cell23_3712404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3712404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712404 prefixEnd_3712404 := by exact prefixLift 3712404
  have htrace : WordTrace (prefixWord ++ tailWord_3712404) baseStart_3712404 baseEnd_3712404 := by
    simpa [prefixWord, tailWord_3712404, baseEnd_3712404] using wordTrace_append hprefix tailTrace_3712404
  have hstable : (prefixWord ++ tailWord_3712404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712404).length < 2 ^ (prefixWord ++ tailWord_3712404).sum := by decide
  have hdescent : baseEnd_3712404 < baseStart_3712404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712414 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3712414 : Nat := 118140960795 + 3712414 * 2 ^ 59
def prefixEnd_3712414 : Nat := 4983230072969 + 3 ^ 40 * 3712414 * 2
def baseEnd_3712414 : Nat := 635417590160181132283975

theorem tailTrace_3712414 : CollatzResearch.WordTrace tailWord_3712414 prefixEnd_3712414 635417590160181132283975 := by
  unfold tailWord_3712414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16925357796570697834827037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90268574915043721785744197 16925357796570697834827037)
  ·
    refine ⟨6347009173714011688060139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16925357796570697834827037 6347009173714011688060139)
    ·
      refine ⟨9520513760571017532090209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6347009173714011688060139 9520513760571017532090209)
      ·
        refine ⟨7140385320428263149067657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9520513760571017532090209 7140385320428263149067657)
        ·
          refine ⟨5355288990321197361800743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7140385320428263149067657 5355288990321197361800743)
          ·
            refine ⟨8032933485481796042701115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355288990321197361800743 8032933485481796042701115)
            ·
              refine ⟨12049400228222694064051673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8032933485481796042701115 12049400228222694064051673)
              ·
                refine ⟨9037050171167020548038755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12049400228222694064051673 9037050171167020548038755)
                ·
                  refine ⟨13555575256750530822058133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9037050171167020548038755 13555575256750530822058133)
                  ·
                    refine ⟨635417590160181132283975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13555575256750530822058133 635417590160181132283975)
                    ·
                      rfl

theorem cell23_3712414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3712414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712414 prefixEnd_3712414 := by exact prefixLift 3712414
  have htrace : WordTrace (prefixWord ++ tailWord_3712414) baseStart_3712414 baseEnd_3712414 := by
    simpa [prefixWord, tailWord_3712414, baseEnd_3712414] using wordTrace_append hprefix tailTrace_3712414
  have hstable : (prefixWord ++ tailWord_3712414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712414).length < 2 ^ (prefixWord ++ tailWord_3712414).sum := by decide
  have hdescent : baseEnd_3712414 < baseStart_3712414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712444 : List Nat := [2, 2, 2, 4, 3, 1, 1, 8]
def baseStart_3712444 : Nat := 118140960795 + 3712444 * 2 ^ 59
def prefixEnd_3712444 : Nat := 4983230072969 + 3 ^ 40 * 3712444 * 2
def baseEnd_3712444 : Nat := 70602524996302899239881

theorem tailTrace_3712444 : CollatzResearch.WordTrace tailWord_3712444 prefixEnd_3712444 70602524996302899239881 := by
  unfold tailWord_3712444
  simp only [CollatzResearch.WordTrace]
  refine ⟨67701978281228448901104193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90269304374971265201472257 67701978281228448901104193)
  ·
    refine ⟨50776483710921336675828145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67701978281228448901104193 50776483710921336675828145)
    ·
      refine ⟨38082362783191002506871109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50776483710921336675828145 38082362783191002506871109)
      ·
        refine ⟨7140443021848312970038333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38082362783191002506871109 7140443021848312970038333)
        ·
          refine ⟨2677666133193117363764375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7140443021848312970038333 2677666133193117363764375)
          ·
            refine ⟨4016499199789676045646563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677666133193117363764375 4016499199789676045646563)
            ·
              refine ⟨6024748799684514068469845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016499199789676045646563 6024748799684514068469845)
              ·
                refine ⟨70602524996302899239881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6024748799684514068469845 70602524996302899239881)
                ·
                  rfl

theorem cell23_3712444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 8].length) (baseStart_3712444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712444 prefixEnd_3712444 := by exact prefixLift 3712444
  have htrace : WordTrace (prefixWord ++ tailWord_3712444) baseStart_3712444 baseEnd_3712444 := by
    simpa [prefixWord, tailWord_3712444, baseEnd_3712444] using wordTrace_append hprefix tailTrace_3712444
  have hstable : (prefixWord ++ tailWord_3712444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712444).length < 2 ^ (prefixWord ++ tailWord_3712444).sum := by decide
  have hdescent : baseEnd_3712444 < baseStart_3712444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712480 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3]
def baseStart_3712480 : Nat := 118140960795 + 3712480 * 2 ^ 59
def prefixEnd_3712480 : Nat := 4983230072969 + 3 ^ 40 * 3712480 * 2
def baseEnd_3712480 : Nat := 1906286660203740138626621

theorem tailTrace_3712480 : CollatzResearch.WordTrace tailWord_3712480 prefixEnd_3712480 1906286660203740138626621 := by
  unfold tailWord_3712480
  simp only [CollatzResearch.WordTrace]
  refine ⟨67702634795163237975259447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90270179726884317300345929 67702634795163237975259447)
  ·
    refine ⟨101553952192744856962889171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67702634795163237975259447 101553952192744856962889171)
    ·
      refine ⟨152330928289117285444333757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101553952192744856962889171 152330928289117285444333757)
      ·
        refine ⟨57124098108418982041625159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152330928289117285444333757 57124098108418982041625159)
        ·
          refine ⟨85686147162628473062437739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57124098108418982041625159 85686147162628473062437739)
          ·
            refine ⟨128529220743942709593656609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85686147162628473062437739 128529220743942709593656609)
            ·
              refine ⟨96396915557957032195242457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128529220743942709593656609 96396915557957032195242457)
              ·
                refine ⟨72297686668467774146431843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96396915557957032195242457 72297686668467774146431843)
                ·
                  refine ⟨108446530002701661219647765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72297686668467774146431843 108446530002701661219647765)
                  ·
                    refine ⟨5083431093876640369670989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108446530002701661219647765 5083431093876640369670989)
                    ·
                      refine ⟨1906286660203740138626621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5083431093876640369670989 1906286660203740138626621)
                      ·
                        rfl

theorem cell23_3712480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_3712480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712480 prefixEnd_3712480 := by exact prefixLift 3712480
  have htrace : WordTrace (prefixWord ++ tailWord_3712480) baseStart_3712480 baseEnd_3712480 := by
    simpa [prefixWord, tailWord_3712480, baseEnd_3712480] using wordTrace_append hprefix tailTrace_3712480
  have hstable : (prefixWord ++ tailWord_3712480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712480).length < 2 ^ (prefixWord ++ tailWord_3712480).sum := by decide
  have hdescent : baseEnd_3712480 < baseStart_3712480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712481 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_3712481 : Nat := 118140960795 + 3712481 * 2 ^ 59
def prefixEnd_3712481 : Nat := 4983230072969 + 3 ^ 40 * 3712481 * 2
def baseEnd_3712481 : Nat := 1906287173684394634714117

theorem tailTrace_3712481 : CollatzResearch.WordTrace tailWord_3712481 prefixEnd_3712481 1906287173684394634714117 := by
  unfold tailWord_3712481
  simp only [CollatzResearch.WordTrace]
  refine ⟨135405306063322853121305297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90270204042215235414203531 135405306063322853121305297)
  ·
    refine ⟨101553979547492139840978973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135405306063322853121305297 101553979547492139840978973)
    ·
      refine ⟨38082742330309552440367115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101553979547492139840978973 38082742330309552440367115)
      ·
        refine ⟨57124113495464328660550673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38082742330309552440367115 57124113495464328660550673)
        ·
          refine ⟨42843085121598246495413005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57124113495464328660550673 42843085121598246495413005)
          ·
            refine ⟨16066156920599342435779877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42843085121598246495413005 16066156920599342435779877)
            ·
              refine ⟨3012404422612376706708727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16066156920599342435779877 3012404422612376706708727)
              ·
                refine ⟨4518606633918565060063091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012404422612376706708727 4518606633918565060063091)
                ·
                  refine ⟨6777909950877847590094637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518606633918565060063091 6777909950877847590094637)
                  ·
                    refine ⟨2541716231579192846285489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6777909950877847590094637 2541716231579192846285489)
                    ·
                      refine ⟨1906287173684394634714117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541716231579192846285489 1906287173684394634714117)
                      ·
                        rfl

theorem cell23_3712481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_3712481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712481 prefixEnd_3712481 := by exact prefixLift 3712481
  have htrace : WordTrace (prefixWord ++ tailWord_3712481) baseStart_3712481 baseEnd_3712481 := by
    simpa [prefixWord, tailWord_3712481, baseEnd_3712481] using wordTrace_append hprefix tailTrace_3712481
  have hstable : (prefixWord ++ tailWord_3712481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712481).length < 2 ^ (prefixWord ++ tailWord_3712481).sum := by decide
  have hdescent : baseEnd_3712481 < baseStart_3712481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712554 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_3712554 : Nat := 118140960795 + 3712554 * 2 ^ 59
def prefixEnd_3712554 : Nat := 4983230072969 + 3 ^ 40 * 3712554 * 2
def baseEnd_3712554 : Nat := 1906324657772172849101281

theorem tailTrace_3712554 : CollatzResearch.WordTrace tailWord_3712554 prefixEnd_3712554 1906324657772172849101281 := by
  unfold tailWord_3712554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33851992148014596647178179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90271979061372257725808477 33851992148014596647178179)
  ·
    refine ⟨50777988222021894970767269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33851992148014596647178179 50777988222021894970767269)
    ·
      refine ⟨9520872791629105307018863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50777988222021894970767269 9520872791629105307018863)
      ·
        refine ⟨14281309187443657960528295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9520872791629105307018863 14281309187443657960528295)
        ·
          refine ⟨21421963781165486940792443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14281309187443657960528295 21421963781165486940792443)
          ·
            refine ⟨32132945671748230411188665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21421963781165486940792443 32132945671748230411188665)
            ·
              refine ⟨24099709253811172808391499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32132945671748230411188665 24099709253811172808391499)
              ·
                refine ⟨36149563880716759212587249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24099709253811172808391499 36149563880716759212587249)
                ·
                  refine ⟨27112172910537569409440437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36149563880716759212587249 27112172910537569409440437)
                  ·
                    refine ⟨2541766210362897132135041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27112172910537569409440437 2541766210362897132135041)
                    ·
                      refine ⟨1906324657772172849101281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541766210362897132135041 1906324657772172849101281)
                      ·
                        rfl

theorem cell23_3712554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_3712554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712554 prefixEnd_3712554 := by exact prefixLift 3712554
  have htrace : WordTrace (prefixWord ++ tailWord_3712554) baseStart_3712554 baseEnd_3712554 := by
    simpa [prefixWord, tailWord_3712554, baseEnd_3712554] using wordTrace_append hprefix tailTrace_3712554
  have hstable : (prefixWord ++ tailWord_3712554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712554).length < 2 ^ (prefixWord ++ tailWord_3712554).sum := by decide
  have hdescent : baseEnd_3712554 < baseStart_3712554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712611 : List Nat := [1, 1, 1, 5, 1, 4, 1, 4, 1, 4]
def baseStart_3712611 : Nat := 118140960795 + 3712611 * 2 ^ 59
def prefixEnd_3712611 : Nat := 4983230072969 + 3 ^ 40 * 3712611 * 2
def baseEnd_3712611 : Nat := 635451308723159708696173

theorem tailTrace_3712611 : CollatzResearch.WordTrace tailWord_3712611 prefixEnd_3712611 635451308723159708696173 := by
  unfold tailWord_3712611
  simp only [CollatzResearch.WordTrace]
  refine ⟨135410047552851885323537687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90273365035234590215691791 135410047552851885323537687)
  ·
    refine ⟨203115071329277827985306531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135410047552851885323537687 203115071329277827985306531)
    ·
      refine ⟨304672606993916741977959797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203115071329277827985306531 304672606993916741977959797)
      ·
        refine ⟨28563056905679694560433731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304672606993916741977959797 28563056905679694560433731)
        ·
          refine ⟨42844585358519541840650597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28563056905679694560433731 42844585358519541840650597)
          ·
            refine ⟨8033359754722414095121987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42844585358519541840650597 8033359754722414095121987)
            ·
              refine ⟨12050039632083621142682981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8033359754722414095121987 12050039632083621142682981)
              ·
                refine ⟨2259382431015678964253059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12050039632083621142682981 2259382431015678964253059)
                ·
                  refine ⟨3389073646523518446379589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259382431015678964253059 3389073646523518446379589)
                  ·
                    refine ⟨635451308723159708696173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389073646523518446379589 635451308723159708696173)
                    ·
                      rfl

theorem cell23_3712611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 4].length) (baseStart_3712611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712611 prefixEnd_3712611 := by exact prefixLift 3712611
  have htrace : WordTrace (prefixWord ++ tailWord_3712611) baseStart_3712611 baseEnd_3712611 := by
    simpa [prefixWord, tailWord_3712611, baseEnd_3712611] using wordTrace_append hprefix tailTrace_3712611
  have hstable : (prefixWord ++ tailWord_3712611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712611).length < 2 ^ (prefixWord ++ tailWord_3712611).sum := by decide
  have hdescent : baseEnd_3712611 < baseStart_3712611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712657 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_3712657 : Nat := 118140960795 + 3712657 * 2 ^ 59
def prefixEnd_3712657 : Nat := 4983230072969 + 3 ^ 40 * 3712657 * 2
def baseEnd_3712657 : Nat := 1906377546279585946113307

theorem tailTrace_3712657 : CollatzResearch.WordTrace tailWord_3712657 prefixEnd_3712657 1906377546279585946113307 := by
  unfold tailWord_3712657
  simp only [CollatzResearch.WordTrace]
  refine ⟨135411725310685235179712225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90274483540456823453141483 135411725310685235179712225)
  ·
    refine ⟨101558793983013926384784169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135411725310685235179712225 101558793983013926384784169)
    ·
      refine ⟨76169095487260444788588127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101558793983013926384784169 76169095487260444788588127)
      ·
        refine ⟨114253643230890667182882191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76169095487260444788588127 114253643230890667182882191)
        ·
          refine ⟨171380464846336000774323287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114253643230890667182882191 171380464846336000774323287)
          ·
            refine ⟨257070697269504001161484931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171380464846336000774323287 257070697269504001161484931)
            ·
              refine ⟨385606045904256001742227397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257070697269504001161484931 385606045904256001742227397)
              ·
                refine ⟨72301133607048000326667637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385606045904256001742227397 72301133607048000326667637)
                ·
                  refine ⟨6778231275660750030625091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72301133607048000326667637 6778231275660750030625091)
                  ·
                    refine ⟨10167346913491125045937637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6778231275660750030625091 10167346913491125045937637)
                    ·
                      refine ⟨1906377546279585946113307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10167346913491125045937637 1906377546279585946113307)
                      ·
                        rfl

theorem cell23_3712657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_3712657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712657 prefixEnd_3712657 := by exact prefixLift 3712657
  have htrace : WordTrace (prefixWord ++ tailWord_3712657) baseStart_3712657 baseEnd_3712657 := by
    simpa [prefixWord, tailWord_3712657, baseEnd_3712657] using wordTrace_append hprefix tailTrace_3712657
  have hstable : (prefixWord ++ tailWord_3712657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712657).length < 2 ^ (prefixWord ++ tailWord_3712657).sum := by decide
  have hdescent : baseEnd_3712657 < baseStart_3712657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712658 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 6]
def baseStart_3712658 : Nat := 118140960795 + 3712658 * 2 ^ 59
def prefixEnd_3712658 : Nat := 4983230072969 + 3 ^ 40 * 3712658 * 2
def baseEnd_3712658 : Nat := 211819784417804493577867

theorem tailTrace_3712658 : CollatzResearch.WordTrace tailWord_3712658 prefixEnd_3712658 211819784417804493577867 := by
  unfold tailWord_3712658
  simp only [CollatzResearch.WordTrace]
  refine ⟨33852940445920403087624657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90274507855787741566999085 33852940445920403087624657)
  ·
    refine ⟨25389705334440302315718493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33852940445920403087624657 25389705334440302315718493)
    ·
      refine ⟨9521139500415113368394435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25389705334440302315718493 9521139500415113368394435)
      ·
        refine ⟨14281709250622670052591653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9521139500415113368394435 14281709250622670052591653)
        ·
          refine ⟨2677820484491750634860935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14281709250622670052591653 2677820484491750634860935)
          ·
            refine ⟨4016730726737625952291403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677820484491750634860935 4016730726737625952291403)
            ·
              refine ⟨6025096090106438928437105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016730726737625952291403 6025096090106438928437105)
              ·
                refine ⟨4518822067579829196327829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025096090106438928437105 4518822067579829196327829)
                ·
                  refine ⟨211819784417804493577867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4518822067579829196327829 211819784417804493577867)
                  ·
                    rfl

theorem cell23_3712658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_3712658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712658 prefixEnd_3712658 := by exact prefixLift 3712658
  have htrace : WordTrace (prefixWord ++ tailWord_3712658) baseStart_3712658 baseEnd_3712658 := by
    simpa [prefixWord, tailWord_3712658, baseEnd_3712658] using wordTrace_append hprefix tailTrace_3712658
  have hstable : (prefixWord ++ tailWord_3712658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712658).length < 2 ^ (prefixWord ++ tailWord_3712658).sum := by decide
  have hdescent : baseEnd_3712658 < baseStart_3712658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712668 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3712668 : Nat := 118140960795 + 3712668 * 2 ^ 59
def prefixEnd_3712668 : Nat := 4983230072969 + 3 ^ 40 * 3712668 * 2
def baseEnd_3712668 : Nat := 1906383194566785403075757

theorem tailTrace_3712668 : CollatzResearch.WordTrace tailWord_3712668 prefixEnd_3712668 1906383194566785403075757 := by
  unfold tailWord_3712668
  simp only [CollatzResearch.WordTrace]
  refine ⟨67706063256822692029181329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90274751009096922705575105 67706063256822692029181329)
  ·
    refine ⟨50779547442617019021885997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67706063256822692029181329 50779547442617019021885997)
    ·
      refine ⟨19042330290981382133207249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50779547442617019021885997 19042330290981382133207249)
      ·
        refine ⟨14281747718236036599905437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19042330290981382133207249 14281747718236036599905437)
        ·
          refine ⟨5355655394338513724964539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14281747718236036599905437 5355655394338513724964539)
          ·
            refine ⟨8033483091507770587446809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355655394338513724964539 8033483091507770587446809)
            ·
              refine ⟨6025112318630827940585107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8033483091507770587446809 6025112318630827940585107)
              ·
                refine ⟨9037668477946241910877661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025112318630827940585107 9037668477946241910877661)
                ·
                  refine ⟨3389125679229840716579123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9037668477946241910877661 3389125679229840716579123)
                  ·
                    refine ⟨5083688518844761074868685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389125679229840716579123 5083688518844761074868685)
                    ·
                      refine ⟨1906383194566785403075757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5083688518844761074868685 1906383194566785403075757)
                      ·
                        rfl

theorem cell23_3712668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3712668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712668 prefixEnd_3712668 := by exact prefixLift 3712668
  have htrace : WordTrace (prefixWord ++ tailWord_3712668) baseStart_3712668 baseEnd_3712668 := by
    simpa [prefixWord, tailWord_3712668, baseEnd_3712668] using wordTrace_append hprefix tailTrace_3712668
  have hstable : (prefixWord ++ tailWord_3712668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712668).length < 2 ^ (prefixWord ++ tailWord_3712668).sum := by decide
  have hdescent : baseEnd_3712668 < baseStart_3712668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712677 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3712677 : Nat := 118140960795 + 3712677 * 2 ^ 59
def prefixEnd_3712677 : Nat := 4983230072969 + 3 ^ 40 * 3712677 * 2
def baseEnd_3712677 : Nat := 1906387815892675867863215

theorem tailTrace_3712677 : CollatzResearch.WordTrace tailWord_3712677 prefixEnd_3712677 1906387815892675867863215 := by
  unfold tailWord_3712677
  simp only [CollatzResearch.WordTrace]
  refine ⟨135412454770612778595440285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90274969847075185730293523 135412454770612778595440285)
  ·
    refine ⟨50779670538979791973290107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135412454770612778595440285 50779670538979791973290107)
    ·
      refine ⟨76169505808469687959935161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50779670538979791973290107 76169505808469687959935161)
      ·
        refine ⟨57127129356352265969951371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76169505808469687959935161 57127129356352265969951371)
        ·
          refine ⟨85690694034528398954927057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57127129356352265969951371 85690694034528398954927057)
          ·
            refine ⟨64268020525896299216195293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85690694034528398954927057 64268020525896299216195293)
            ·
              refine ⟨24100507697211112206073235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64268020525896299216195293 24100507697211112206073235)
              ·
                refine ⟨36150761545816668309109853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24100507697211112206073235 36150761545816668309109853)
                ·
                  refine ⟨13556535579681250615916195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36150761545816668309109853 13556535579681250615916195)
                  ·
                    refine ⟨20334803369521875923874293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13556535579681250615916195 20334803369521875923874293)
                    ·
                      refine ⟨1906387815892675867863215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20334803369521875923874293 1906387815892675867863215)
                      ·
                        rfl

theorem cell23_3712677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3712677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712677 prefixEnd_3712677 := by exact prefixLift 3712677
  have htrace : WordTrace (prefixWord ++ tailWord_3712677) baseStart_3712677 baseEnd_3712677 := by
    simpa [prefixWord, tailWord_3712677, baseEnd_3712677] using wordTrace_append hprefix tailTrace_3712677
  have hstable : (prefixWord ++ tailWord_3712677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712677).length < 2 ^ (prefixWord ++ tailWord_3712677).sum := by decide
  have hdescent : baseEnd_3712677 < baseStart_3712677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712687 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_3712687 : Nat := 118140960795 + 3712687 * 2 ^ 59
def prefixEnd_3712687 : Nat := 4983230072969 + 3 ^ 40 * 3712687 * 2
def baseEnd_3712687 : Nat := 1906392950699220828738169

theorem tailTrace_3712687 : CollatzResearch.WordTrace tailWord_3712687 prefixEnd_3712687 1906392950699220828738169 := by
  unfold tailWord_3712687
  simp only [CollatzResearch.WordTrace]
  refine ⟨135412819500576550303304315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90275213000384366868869543 135412819500576550303304315)
  ·
    refine ⟨203119229250864825454956473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135412819500576550303304315 203119229250864825454956473)
    ·
      refine ⟨152339421938148619091217355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203119229250864825454956473 152339421938148619091217355)
      ·
        refine ⟨228509132907222928636826033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152339421938148619091217355 228509132907222928636826033)
        ·
          refine ⟨171381849680417196477619525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228509132907222928636826033 171381849680417196477619525)
          ·
            refine ⟨32134096815078224339553661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171381849680417196477619525 32134096815078224339553661)
            ·
              refine ⟨12050286305654334127332623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32134096815078224339553661 12050286305654334127332623)
              ·
                refine ⟨18075429458481501190998935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12050286305654334127332623 18075429458481501190998935)
                ·
                  refine ⟨27113144187722251786498403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18075429458481501190998935 27113144187722251786498403)
                  ·
                    refine ⟨40669716281583377679747605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27113144187722251786498403 40669716281583377679747605)
                    ·
                      refine ⟨1906392950699220828738169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40669716281583377679747605 1906392950699220828738169)
                      ·
                        rfl

theorem cell23_3712687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_3712687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712687 prefixEnd_3712687 := by exact prefixLift 3712687
  have htrace : WordTrace (prefixWord ++ tailWord_3712687) baseStart_3712687 baseEnd_3712687 := by
    simpa [prefixWord, tailWord_3712687, baseEnd_3712687] using wordTrace_append hprefix tailTrace_3712687
  have hstable : (prefixWord ++ tailWord_3712687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712687).length < 2 ^ (prefixWord ++ tailWord_3712687).sum := by decide
  have hdescent : baseEnd_3712687 < baseStart_3712687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712691 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 3, 2, 2]
def baseStart_3712691 : Nat := 118140960795 + 3712691 * 2 ^ 59
def prefixEnd_3712691 : Nat := 4983230072969 + 3 ^ 40 * 3712691 * 2
def baseEnd_3712691 : Nat := 1906395004621838813088151

theorem tailTrace_3712691 : CollatzResearch.WordTrace tailWord_3712691 prefixEnd_3712691 1906395004621838813088151 := by
  unfold tailWord_3712691
  simp only [CollatzResearch.WordTrace]
  refine ⟨135412965392562058986449927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90275310261708039324299951 135412965392562058986449927)
  ·
    refine ⟨203119448088843088479674891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135412965392562058986449927 203119448088843088479674891)
    ·
      refine ⟨304679172133264632719512337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203119448088843088479674891 304679172133264632719512337)
      ·
        refine ⟨228509379099948474539634253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304679172133264632719512337 228509379099948474539634253)
        ·
          refine ⟨85691017162480677952362845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228509379099948474539634253 85691017162480677952362845)
          ·
            refine ⟨32134131435930254232136067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85691017162480677952362845 32134131435930254232136067)
            ·
              refine ⟨48201197153895381348204101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32134131435930254232136067 48201197153895381348204101)
              ·
                refine ⟨9037724466355384002788269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48201197153895381348204101 9037724466355384002788269)
                ·
                  refine ⟨3389146674883269001045601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9037724466355384002788269 3389146674883269001045601)
                  ·
                    refine ⟨2541860006162451750784201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3389146674883269001045601 2541860006162451750784201)
                    ·
                      refine ⟨1906395004621838813088151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541860006162451750784201 1906395004621838813088151)
                      ·
                        rfl

theorem cell23_3712691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 2, 2].length) (baseStart_3712691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712691 prefixEnd_3712691 := by exact prefixLift 3712691
  have htrace : WordTrace (prefixWord ++ tailWord_3712691) baseStart_3712691 baseEnd_3712691 := by
    simpa [prefixWord, tailWord_3712691, baseEnd_3712691] using wordTrace_append hprefix tailTrace_3712691
  have hstable : (prefixWord ++ tailWord_3712691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712691).length < 2 ^ (prefixWord ++ tailWord_3712691).sum := by decide
  have hdescent : baseEnd_3712691 < baseStart_3712691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712714 : List Nat := [3, 1, 2, 1, 5, 2, 9]
def baseStart_3712714 : Nat := 118140960795 + 3712714 * 2 ^ 59
def prefixEnd_3712714 : Nat := 4983230072969 + 3 ^ 40 * 3712714 * 2
def baseEnd_3712714 : Nat := 23535886600949286704945

theorem tailTrace_3712714 : CollatzResearch.WordTrace tailWord_3712714 prefixEnd_3712714 23535886600949286704945 := by
  unfold tailWord_3712714
  simp only [CollatzResearch.WordTrace]
  refine ⟨33853451067869683478634299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90275869514319155943024797 33853451067869683478634299)
  ·
    refine ⟨50780176601804525217951449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33853451067869683478634299 50780176601804525217951449)
    ·
      refine ⟨38085132451353393913463587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50780176601804525217951449 38085132451353393913463587)
      ·
        refine ⟨57127698677030090870195381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38085132451353393913463587 57127698677030090870195381)
        ·
          refine ⟨5355721750971571019080817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57127698677030090870195381 5355721750971571019080817)
          ·
            refine ⟨4016791313228678264310613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5355721750971571019080817 4016791313228678264310613)
            ·
              refine ⟨23535886600949286704945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4016791313228678264310613 23535886600949286704945)
              ·
                rfl

theorem cell23_3712714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 9].length) (baseStart_3712714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712714 prefixEnd_3712714 := by exact prefixLift 3712714
  have htrace : WordTrace (prefixWord ++ tailWord_3712714) baseStart_3712714 baseEnd_3712714 := by
    simpa [prefixWord, tailWord_3712714, baseEnd_3712714] using wordTrace_append hprefix tailTrace_3712714
  have hstable : (prefixWord ++ tailWord_3712714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712714).length < 2 ^ (prefixWord ++ tailWord_3712714).sum := by decide
  have hdescent : baseEnd_3712714 < baseStart_3712714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712727 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 2, 7]
def baseStart_3712727 : Nat := 118140960795 + 3712727 * 2 ^ 59
def prefixEnd_3712727 : Nat := 4983230072969 + 3 ^ 40 * 3712727 * 2
def baseEnd_3712727 : Nat := 635471163308466890745995

theorem tailTrace_3712727 : CollatzResearch.WordTrace tailWord_3712727 prefixEnd_3712727 635471163308466890745995 := by
  unfold tailWord_3712727
  simp only [CollatzResearch.WordTrace]
  refine ⟨135414278420431637134760435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90276185613621091423173623 135414278420431637134760435)
  ·
    refine ⟨203121417630647455702140653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135414278420431637134760435 203121417630647455702140653)
    ·
      refine ⟨76170531611492795888302745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203121417630647455702140653 76170531611492795888302745)
      ·
        refine ⟨57127898708619596916227059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76170531611492795888302745 57127898708619596916227059)
        ·
          refine ⟨85691848062929395374340589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57127898708619596916227059 85691848062929395374340589)
          ·
            refine ⟨32134443023598523265377721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85691848062929395374340589 32134443023598523265377721)
            ·
              refine ⟨24100832267698892449033291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32134443023598523265377721 24100832267698892449033291)
              ·
                refine ⟨36151248401548338673549937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24100832267698892449033291 36151248401548338673549937)
                ·
                  refine ⟨27113436301161254005162453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36151248401548338673549937 27113436301161254005162453)
                  ·
                    refine ⟨635471163308466890745995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27113436301161254005162453 635471163308466890745995)
                    ·
                      rfl

theorem cell23_3712727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_3712727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712727 prefixEnd_3712727 := by exact prefixLift 3712727
  have htrace : WordTrace (prefixWord ++ tailWord_3712727) baseStart_3712727 baseEnd_3712727 := by
    simpa [prefixWord, tailWord_3712727, baseEnd_3712727] using wordTrace_append hprefix tailTrace_3712727
  have hstable : (prefixWord ++ tailWord_3712727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712727).length < 2 ^ (prefixWord ++ tailWord_3712727).sum := by decide
  have hdescent : baseEnd_3712727 < baseStart_3712727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712751 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 3, 3, 2]
def baseStart_3712751 : Nat := 118140960795 + 3712751 * 2 ^ 59
def prefixEnd_3712751 : Nat := 4983230072969 + 3 ^ 40 * 3712751 * 2
def baseEnd_3712751 : Nat := 1906425813461108578337875

theorem tailTrace_3712751 : CollatzResearch.WordTrace tailWord_3712751 prefixEnd_3712751 1906425813461108578337875 := by
  unfold tailWord_3712751
  simp only [CollatzResearch.WordTrace]
  refine ⟨135415153772344689233634107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90276769181563126155756071 135415153772344689233634107)
  ·
    refine ⟨203122730658517033850451161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135415153772344689233634107 203122730658517033850451161)
    ·
      refine ⟨152342047993887775387838371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203122730658517033850451161 152342047993887775387838371)
      ·
        refine ⟨228513071990831663081757557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152342047993887775387838371 228513071990831663081757557)
        ·
          refine ⟨21423100499140468413914771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228513071990831663081757557 21423100499140468413914771)
          ·
            refine ⟨32134650748710702620872157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21423100499140468413914771 32134650748710702620872157)
            ·
              refine ⟨12050494030766513482827059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32134650748710702620872157 12050494030766513482827059)
              ·
                refine ⟨18075741046149770224240589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12050494030766513482827059 18075741046149770224240589)
                ·
                  refine ⟨6778402892306163834090221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18075741046149770224240589 6778402892306163834090221)
                  ·
                    refine ⟨2541901084614811437783833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6778402892306163834090221 2541901084614811437783833)
                    ·
                      refine ⟨1906425813461108578337875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2541901084614811437783833 1906425813461108578337875)
                      ·
                        rfl

theorem cell23_3712751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3, 2].length) (baseStart_3712751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712751 prefixEnd_3712751 := by exact prefixLift 3712751
  have htrace : WordTrace (prefixWord ++ tailWord_3712751) baseStart_3712751 baseEnd_3712751 := by
    simpa [prefixWord, tailWord_3712751, baseEnd_3712751] using wordTrace_append hprefix tailTrace_3712751
  have hstable : (prefixWord ++ tailWord_3712751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712751).length < 2 ^ (prefixWord ++ tailWord_3712751).sum := by decide
  have hdescent : baseEnd_3712751 < baseStart_3712751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712775 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3712775 : Nat := 118140960795 + 3712775 * 2 ^ 59
def prefixEnd_3712775 : Nat := 4983230072969 + 3 ^ 40 * 3712775 * 2
def baseEnd_3712775 : Nat := 1906438136996816484437765

theorem tailTrace_3712775 : CollatzResearch.WordTrace tailWord_3712775 prefixEnd_3712775 1906438136996816484437765 := by
  unfold tailWord_3712775
  simp only [CollatzResearch.WordTrace]
  refine ⟨135416029124257741332507779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90277352749505160888338519 135416029124257741332507779)
  ·
    refine ⟨203124043686386611998761669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135416029124257741332507779 203124043686386611998761669)
    ·
      refine ⟨38085758191197489749767813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203124043686386611998761669 38085758191197489749767813)
      ·
        refine ⟨7141079660849529328081465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38085758191197489749767813 7141079660849529328081465)
        ·
          refine ⟨5355809745637146996061099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7141079660849529328081465 5355809745637146996061099)
          ·
            refine ⟨8033714618455720494091649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355809745637146996061099 8033714618455720494091649)
            ·
              refine ⟨6025285963841790370568737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8033714618455720494091649 6025285963841790370568737)
              ·
                refine ⟨4518964472881342777926553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025285963841790370568737 4518964472881342777926553)
                ·
                  refine ⟨3389223354661007083444915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4518964472881342777926553 3389223354661007083444915)
                  ·
                    refine ⟨5083835031991510625167373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389223354661007083444915 5083835031991510625167373)
                    ·
                      refine ⟨1906438136996816484437765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5083835031991510625167373 1906438136996816484437765)
                      ·
                        rfl

theorem cell23_3712775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3712775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712775 prefixEnd_3712775 := by exact prefixLift 3712775
  have htrace : WordTrace (prefixWord ++ tailWord_3712775) baseStart_3712775 baseEnd_3712775 := by
    simpa [prefixWord, tailWord_3712775, baseEnd_3712775] using wordTrace_append hprefix tailTrace_3712775
  have hstable : (prefixWord ++ tailWord_3712775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712775).length < 2 ^ (prefixWord ++ tailWord_3712775).sum := by decide
  have hdescent : baseEnd_3712775 < baseStart_3712775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712777 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_3712777 : Nat := 118140960795 + 3712777 * 2 ^ 59
def prefixEnd_3712777 : Nat := 4983230072969 + 3 ^ 40 * 3712777 * 2
def baseEnd_3712777 : Nat := 1906439163958125476612755

theorem tailTrace_3712777 : CollatzResearch.WordTrace tailWord_3712777 prefixEnd_3712777 1906439163958125476612755 := by
  unfold tailWord_3712777
  simp only [CollatzResearch.WordTrace]
  refine ⟨135416102070250495674080585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90277401380166997116053723 135416102070250495674080585)
  ·
    refine ⟨101562076552687871755560439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135416102070250495674080585 101562076552687871755560439)
    ·
      refine ⟨152343114829031807633340659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101562076552687871755560439 152343114829031807633340659)
      ·
        refine ⟨228514672243547711450010989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152343114829031807633340659 228514672243547711450010989)
        ·
          refine ⟨85693002091330391793754121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228514672243547711450010989 85693002091330391793754121)
          ·
            refine ⟨64269751568497793845315591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85693002091330391793754121 64269751568497793845315591)
            ·
              refine ⟨96404627352746690767973387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64269751568497793845315591 96404627352746690767973387)
              ·
                refine ⟨144606941029120036151960081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96404627352746690767973387 144606941029120036151960081)
                ·
                  refine ⟨108455205771840027113970061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144606941029120036151960081 108455205771840027113970061)
                  ·
                    refine ⟨40670702164440010167738773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108455205771840027113970061 40670702164440010167738773)
                    ·
                      refine ⟨1906439163958125476612755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40670702164440010167738773 1906439163958125476612755)
                      ·
                        rfl

theorem cell23_3712777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_3712777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712777 prefixEnd_3712777 := by exact prefixLift 3712777
  have htrace : WordTrace (prefixWord ++ tailWord_3712777) baseStart_3712777 baseEnd_3712777 := by
    simpa [prefixWord, tailWord_3712777, baseEnd_3712777] using wordTrace_append hprefix tailTrace_3712777
  have hstable : (prefixWord ++ tailWord_3712777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712777).length < 2 ^ (prefixWord ++ tailWord_3712777).sum := by decide
  have hdescent : baseEnd_3712777 < baseStart_3712777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712794 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3712794 : Nat := 118140960795 + 3712794 * 2 ^ 59
def prefixEnd_3712794 : Nat := 4983230072969 + 3 ^ 40 * 3712794 * 2
def baseEnd_3712794 : Nat := 1906447893129251910100177

theorem tailTrace_3712794 : CollatzResearch.WordTrace tailWord_3712794 prefixEnd_3712794 1906447893129251910100177 := by
  unfold tailWord_3712794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33854180527797226894362359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90277814740792605051632957 33854180527797226894362359)
  ·
    refine ⟨50781270791695840341543539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33854180527797226894362359 50781270791695840341543539)
    ·
      refine ⟨76171906187543760512315309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50781270791695840341543539 76171906187543760512315309)
      ·
        refine ⟨28564464820328910192118241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76171906187543760512315309 28564464820328910192118241)
        ·
          refine ⟨21423348615246682644088681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28564464820328910192118241 21423348615246682644088681)
          ·
            refine ⟨16067511461435011983066511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21423348615246682644088681 16067511461435011983066511)
            ·
              refine ⟨24101267192152517974599767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16067511461435011983066511 24101267192152517974599767)
              ·
                refine ⟨36151900788228776961899651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24101267192152517974599767 36151900788228776961899651)
                ·
                  refine ⟨54227851182343165442849477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36151900788228776961899651 54227851182343165442849477)
                  ·
                    refine ⟨10167722096689343520534277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54227851182343165442849477 10167722096689343520534277)
                    ·
                      refine ⟨1906447893129251910100177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10167722096689343520534277 1906447893129251910100177)
                      ·
                        rfl

theorem cell23_3712794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3712794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712794 prefixEnd_3712794 := by exact prefixLift 3712794
  have htrace : WordTrace (prefixWord ++ tailWord_3712794) baseStart_3712794 baseEnd_3712794 := by
    simpa [prefixWord, tailWord_3712794, baseEnd_3712794] using wordTrace_append hprefix tailTrace_3712794
  have hstable : (prefixWord ++ tailWord_3712794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712794).length < 2 ^ (prefixWord ++ tailWord_3712794).sum := by decide
  have hdescent : baseEnd_3712794 < baseStart_3712794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712804 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 9]
def baseStart_3712804 : Nat := 118140960795 + 3712804 * 2 ^ 59
def prefixEnd_3712804 : Nat := 4983230072969 + 3 ^ 40 * 3712804 * 2
def baseEnd_3712804 : Nat := 211828114215088541219459

theorem tailTrace_3712804 : CollatzResearch.WordTrace tailWord_3712804 prefixEnd_3712804 211828114215088541219459 := by
  unfold tailWord_3712804
  simp only [CollatzResearch.WordTrace]
  refine ⟨67708543420576339642656733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90278057894101786190208977 67708543420576339642656733)
  ·
    refine ⟨25390703782716127365996275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67708543420576339642656733 25390703782716127365996275)
    ·
      refine ⟨38086055674074191048994413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25390703782716127365996275 38086055674074191048994413)
      ·
        refine ⟨14282270877777821643372905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38086055674074191048994413 14282270877777821643372905)
        ·
          refine ⟨10711703158333366232529679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14282270877777821643372905 10711703158333366232529679)
          ·
            refine ⟨16067554737500049348794519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10711703158333366232529679 16067554737500049348794519)
            ·
              refine ⟨24101332106250074023191779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16067554737500049348794519 24101332106250074023191779)
              ·
                refine ⟨36151998159375111034787669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24101332106250074023191779 36151998159375111034787669)
                ·
                  refine ⟨211828114215088541219459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36151998159375111034787669 211828114215088541219459)
                  ·
                    rfl

theorem cell23_3712804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_3712804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712804 prefixEnd_3712804 := by exact prefixLift 3712804
  have htrace : WordTrace (prefixWord ++ tailWord_3712804) baseStart_3712804 baseEnd_3712804 := by
    simpa [prefixWord, tailWord_3712804, baseEnd_3712804] using wordTrace_append hprefix tailTrace_3712804
  have hstable : (prefixWord ++ tailWord_3712804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712804).length < 2 ^ (prefixWord ++ tailWord_3712804).sum := by decide
  have hdescent : baseEnd_3712804 < baseStart_3712804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712838 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3712838 : Nat := 118140960795 + 3712838 * 2 ^ 59
def prefixEnd_3712838 : Nat := 4983230072969 + 3 ^ 40 * 3712838 * 2
def baseEnd_3712838 : Nat := 211830054030894415327775

theorem tailTrace_3712838 : CollatzResearch.WordTrace tailWord_3712838 prefixEnd_3712838 211830054030894415327775 := by
  unfold tailWord_3712838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4231822716344671971626599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90278884615353002061367445 4231822716344671971626599)
  ·
    refine ⟨6347734074517007957439899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4231822716344671971626599 6347734074517007957439899)
    ·
      refine ⟨9521601111775511936159849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6347734074517007957439899 9521601111775511936159849)
      ·
        refine ⟨7141200833831633952119887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9521601111775511936159849 7141200833831633952119887)
        ·
          refine ⟨10711801250747450928179831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141200833831633952119887 10711801250747450928179831)
          ·
            refine ⟨16067701876121176392269747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10711801250747450928179831 16067701876121176392269747)
            ·
              refine ⟨24101552814181764588404621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16067701876121176392269747 24101552814181764588404621)
              ·
                refine ⟨9038082305318161720651733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24101552814181764588404621 9038082305318161720651733)
                ·
                  refine ⟨211830054030894415327775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9038082305318161720651733 211830054030894415327775)
                  ·
                    rfl

theorem cell23_3712838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3712838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712838 prefixEnd_3712838 := by exact prefixLift 3712838
  have htrace : WordTrace (prefixWord ++ tailWord_3712838) baseStart_3712838 baseEnd_3712838 := by
    simpa [prefixWord, tailWord_3712838, baseEnd_3712838] using wordTrace_append hprefix tailTrace_3712838
  have hstable : (prefixWord ++ tailWord_3712838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712838).length < 2 ^ (prefixWord ++ tailWord_3712838).sum := by decide
  have hdescent : baseEnd_3712838 < baseStart_3712838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712871 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_3712871 : Nat := 118140960795 + 3712871 * 2 ^ 59
def prefixEnd_3712871 : Nat := 4983230072969 + 3 ^ 40 * 3712871 * 2
def baseEnd_3712871 : Nat := 1906487431139648108837323

theorem tailTrace_3712871 : CollatzResearch.WordTrace tailWord_3712871 prefixEnd_3712871 1906487431139648108837323 := by
  unfold tailWord_3712871
  simp only [CollatzResearch.WordTrace]
  refine ⟨135419530531909949728002467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90279687021273299818668311 135419530531909949728002467)
  ·
    refine ⟨203129295797864924592003701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135419530531909949728002467 203129295797864924592003701)
    ·
      refine ⟨19043371481049836680500347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203129295797864924592003701 19043371481049836680500347)
      ·
        refine ⟨28565057221574755020750521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19043371481049836680500347 28565057221574755020750521)
        ·
          refine ⟨21423792916181066265562891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28565057221574755020750521 21423792916181066265562891)
          ·
            refine ⟨32135689374271599398344337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21423792916181066265562891 32135689374271599398344337)
            ·
              refine ⟨24101767030703699548758253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32135689374271599398344337 24101767030703699548758253)
              ·
                refine ⟨9038162636513887330784345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24101767030703699548758253 9038162636513887330784345)
                ·
                  refine ⟨6778621977385415498088259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9038162636513887330784345 6778621977385415498088259)
                  ·
                    refine ⟨10167932966078123247132389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6778621977385415498088259 10167932966078123247132389)
                    ·
                      refine ⟨1906487431139648108837323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10167932966078123247132389 1906487431139648108837323)
                      ·
                        rfl

theorem cell23_3712871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_3712871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712871 prefixEnd_3712871 := by exact prefixLift 3712871
  have htrace : WordTrace (prefixWord ++ tailWord_3712871) baseStart_3712871 baseEnd_3712871 := by
    simpa [prefixWord, tailWord_3712871, baseEnd_3712871] using wordTrace_append hprefix tailTrace_3712871
  have hstable : (prefixWord ++ tailWord_3712871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712871).length < 2 ^ (prefixWord ++ tailWord_3712871).sum := by decide
  have hdescent : baseEnd_3712871 < baseStart_3712871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712971 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 1, 6]
def baseStart_3712971 : Nat := 118140960795 + 3712971 * 2 ^ 59
def prefixEnd_3712971 : Nat := 4983230072969 + 3 ^ 40 * 3712971 * 2
def baseEnd_3712971 : Nat := 635512926401699239195621

theorem tailTrace_3712971 : CollatzResearch.WordTrace tailWord_3712971 prefixEnd_3712971 635512926401699239195621 := by
  unfold tailWord_3712971
  simp only [CollatzResearch.WordTrace]
  refine ⟨135423177831547666806642767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90282118554365111204428511 135423177831547666806642767)
  ·
    refine ⟨203134766747321500209964151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135423177831547666806642767 203134766747321500209964151)
    ·
      refine ⟨304702150120982250314946227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203134766747321500209964151 304702150120982250314946227)
      ·
        refine ⟨457053225181473375472419341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304702150120982250314946227 457053225181473375472419341)
        ·
          refine ⟨171394959443052515802157253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457053225181473375472419341 171394959443052515802157253)
          ·
            refine ⟨32136554895572346712904485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171394959443052515802157253 32136554895572346712904485)
            ·
              refine ⟨6025604042919815008669591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32136554895572346712904485 6025604042919815008669591)
              ·
                refine ⟨9038406064379722513004387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025604042919815008669591 9038406064379722513004387)
                ·
                  refine ⟨13557609096569583769506581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9038406064379722513004387 13557609096569583769506581)
                  ·
                    refine ⟨635512926401699239195621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13557609096569583769506581 635512926401699239195621)
                    ·
                      rfl

theorem cell23_3712971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 6].length) (baseStart_3712971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712971 prefixEnd_3712971 := by exact prefixLift 3712971
  have htrace : WordTrace (prefixWord ++ tailWord_3712971) baseStart_3712971 baseEnd_3712971 := by
    simpa [prefixWord, tailWord_3712971, baseEnd_3712971] using wordTrace_append hprefix tailTrace_3712971
  have hstable : (prefixWord ++ tailWord_3712971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712971).length < 2 ^ (prefixWord ++ tailWord_3712971).sum := by decide
  have hdescent : baseEnd_3712971 < baseStart_3712971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712982 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_3712982 : Nat := 118140960795 + 3712982 * 2 ^ 59
def prefixEnd_3712982 : Nat := 4983230072969 + 3 ^ 40 * 3712982 * 2
def baseEnd_3712982 : Nat := 1906544427492297174549313

theorem tailTrace_3712982 : CollatzResearch.WordTrace tailWord_3712982 prefixEnd_3712982 1906544427492297174549313 := by
  unfold tailWord_3712982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463973689656738480330825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90282386023005210456862133 8463973689656738480330825)
  ·
    refine ⟨6347980267242553860248119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8463973689656738480330825 6347980267242553860248119)
    ·
      refine ⟨9521970400863830790372179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6347980267242553860248119 9521970400863830790372179)
      ·
        refine ⟨14282955601295746185558269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9521970400863830790372179 14282955601295746185558269)
        ·
          refine ⟨5356108350485904819584351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14282955601295746185558269 5356108350485904819584351)
          ·
            refine ⟨8034162525728857229376527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356108350485904819584351 8034162525728857229376527)
            ·
              refine ⟨12051243788593285844064791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8034162525728857229376527 12051243788593285844064791)
              ·
                refine ⟨18076865682889928766097187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12051243788593285844064791 18076865682889928766097187)
                ·
                  refine ⟨27115298524334893149145781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18076865682889928766097187 27115298524334893149145781)
                  ·
                    refine ⟨2542059236656396232732417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27115298524334893149145781 2542059236656396232732417)
                    ·
                      refine ⟨1906544427492297174549313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542059236656396232732417 1906544427492297174549313)
                      ·
                        rfl

theorem cell23_3712982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_3712982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712982 prefixEnd_3712982 := by exact prefixLift 3712982
  have htrace : WordTrace (prefixWord ++ tailWord_3712982) baseStart_3712982 baseEnd_3712982 := by
    simpa [prefixWord, tailWord_3712982, baseEnd_3712982] using wordTrace_append hprefix tailTrace_3712982
  have hstable : (prefixWord ++ tailWord_3712982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712982).length < 2 ^ (prefixWord ++ tailWord_3712982).sum := by decide
  have hdescent : baseEnd_3712982 < baseStart_3712982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712989 : List Nat := [1, 4, 3, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_3712989 : Nat := 118140960795 + 3712989 * 2 ^ 59
def prefixEnd_3712989 : Nat := 4983230072969 + 3 ^ 40 * 3712989 * 2
def baseEnd_3712989 : Nat := 1906548021856878647161781

theorem tailTrace_3712989 : CollatzResearch.WordTrace tailWord_3712989 prefixEnd_3712989 1906548021856878647161781 := by
  unfold tailWord_3712989
  simp only [CollatzResearch.WordTrace]
  refine ⟨135423834345482455880798021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90282556230321637253865347 135423834345482455880798021)
  ·
    refine ⟨25391968939777960477649629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135423834345482455880798021 25391968939777960477649629)
    ·
      refine ⟨9521988352416735179118611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25391968939777960477649629 9521988352416735179118611)
      ·
        refine ⟨14282982528625102768677917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9521988352416735179118611 14282982528625102768677917)
        ·
          refine ⟨5356118448234413538254219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14282982528625102768677917 5356118448234413538254219)
          ·
            refine ⟨8034177672351620307381329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356118448234413538254219 8034177672351620307381329)
            ·
              refine ⟨6025633254263715230535997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034177672351620307381329 6025633254263715230535997)
              ·
                refine ⟨2259612470348893211450999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6025633254263715230535997 2259612470348893211450999)
                ·
                  refine ⟨3389418705523339817176499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259612470348893211450999 3389418705523339817176499)
                  ·
                    refine ⟨5084128058285009725764749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389418705523339817176499 5084128058285009725764749)
                    ·
                      refine ⟨1906548021856878647161781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084128058285009725764749 1906548021856878647161781)
                      ·
                        rfl

theorem cell23_3712989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_3712989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712989 prefixEnd_3712989 := by exact prefixLift 3712989
  have htrace : WordTrace (prefixWord ++ tailWord_3712989) baseStart_3712989 baseEnd_3712989 := by
    simpa [prefixWord, tailWord_3712989, baseEnd_3712989] using wordTrace_append hprefix tailTrace_3712989
  have hstable : (prefixWord ++ tailWord_3712989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712989).length < 2 ^ (prefixWord ++ tailWord_3712989).sum := by decide
  have hdescent : baseEnd_3712989 < baseStart_3712989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3712995 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 1, 1, 4]
def baseStart_3712995 : Nat := 118140960795 + 3712995 * 2 ^ 59
def prefixEnd_3712995 : Nat := 4983230072969 + 3 ^ 40 * 3712995 * 2
def baseEnd_3712995 : Nat := 1906551102740805623686753

theorem tailTrace_3712995 : CollatzResearch.WordTrace tailWord_3712995 prefixEnd_3712995 1906551102740805623686753 := by
  unfold tailWord_3712995
  simp only [CollatzResearch.WordTrace]
  refine ⟨135424053183460718905516439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90282702122307145937010959 135424053183460718905516439)
  ·
    refine ⟨203136079775191078358274659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135424053183460718905516439 203136079775191078358274659)
    ·
      refine ⟨304704119662786617537411989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203136079775191078358274659 304704119662786617537411989)
      ·
        refine ⟨14283005609193122697066187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304704119662786617537411989 14283005609193122697066187)
        ·
          refine ⟨21424508413789684045599281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14283005609193122697066187 21424508413789684045599281)
          ·
            refine ⟨16068381310342263034199461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21424508413789684045599281 16068381310342263034199461)
            ·
              refine ⟨3012821495689174318912399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16068381310342263034199461 3012821495689174318912399)
              ·
                refine ⟨4519232243533761478368599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012821495689174318912399 4519232243533761478368599)
                ·
                  refine ⟨6778848365300642217552899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519232243533761478368599 6778848365300642217552899)
                  ·
                    refine ⟨10168272547950963326329349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6778848365300642217552899 10168272547950963326329349)
                    ·
                      refine ⟨1906551102740805623686753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10168272547950963326329349 1906551102740805623686753)
                      ·
                        rfl

theorem cell23_3712995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_3712995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3712995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3712995 prefixEnd_3712995 := by exact prefixLift 3712995
  have htrace : WordTrace (prefixWord ++ tailWord_3712995) baseStart_3712995 baseEnd_3712995 := by
    simpa [prefixWord, tailWord_3712995, baseEnd_3712995] using wordTrace_append hprefix tailTrace_3712995
  have hstable : (prefixWord ++ tailWord_3712995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3712995).length < 2 ^ (prefixWord ++ tailWord_3712995).sum := by decide
  have hdescent : baseEnd_3712995 < baseStart_3712995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3712995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713011 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 3]
def baseStart_3713011 : Nat := 118140960795 + 3713011 * 2 ^ 59
def prefixEnd_3713011 : Nat := 4983230072969 + 3 ^ 40 * 3713011 * 2
def baseEnd_3713011 : Nat := 1906559318431277561086679

theorem tailTrace_3713011 : CollatzResearch.WordTrace tailWord_3713011 prefixEnd_3713011 1906559318431277561086679 := by
  unfold tailWord_3713011
  simp only [CollatzResearch.WordTrace]
  refine ⟨135424636751402753638098887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90283091167601835758732591 135424636751402753638098887)
  ·
    refine ⟨203136955127104130457148331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135424636751402753638098887 203136955127104130457148331)
    ·
      refine ⟨304705432690656195685722497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203136955127104130457148331 304705432690656195685722497)
      ·
        refine ⟨228529074517992146764291873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304705432690656195685722497 228529074517992146764291873)
        ·
          refine ⟨171396805888494110073218905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228529074517992146764291873 171396805888494110073218905)
          ·
            refine ⟨128547604416370582554914179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171396805888494110073218905 128547604416370582554914179)
            ·
              refine ⟨192821406624555873832371269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128547604416370582554914179 192821406624555873832371269)
              ·
                refine ⟨36154013742104226343569613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192821406624555873832371269 36154013742104226343569613)
                ·
                  refine ⟨13557755153289084878838605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36154013742104226343569613 13557755153289084878838605)
                  ·
                    refine ⟨5084158182483406829564477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13557755153289084878838605 5084158182483406829564477)
                    ·
                      refine ⟨1906559318431277561086679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084158182483406829564477 1906559318431277561086679)
                      ·
                        rfl

theorem cell23_3713011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_3713011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713011 prefixEnd_3713011 := by exact prefixLift 3713011
  have htrace : WordTrace (prefixWord ++ tailWord_3713011) baseStart_3713011 baseEnd_3713011 := by
    simpa [prefixWord, tailWord_3713011, baseEnd_3713011] using wordTrace_append hprefix tailTrace_3713011
  have hstable : (prefixWord ++ tailWord_3713011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713011).length < 2 ^ (prefixWord ++ tailWord_3713011).sum := by decide
  have hdescent : baseEnd_3713011 < baseStart_3713011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713055 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 1, 3, 2]
def baseStart_3713055 : Nat := 118140960795 + 3713055 * 2 ^ 59
def prefixEnd_3713055 : Nat := 4983230072969 + 3 ^ 40 * 3713055 * 2
def baseEnd_3713055 : Nat := 1906581911580075388936477

theorem tailTrace_3713055 : CollatzResearch.WordTrace tailWord_3713055 prefixEnd_3713055 1906581911580075388936477 := by
  unfold tailWord_3713055
  simp only [CollatzResearch.WordTrace]
  refine ⟨135426241563243349152700619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90284161042162232768467079 135426241563243349152700619)
  ·
    refine ⟨203139362344865023729050929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135426241563243349152700619 203139362344865023729050929)
    ·
      refine ⟨152354521758648767796788197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203139362344865023729050929 152354521758648767796788197)
      ·
        refine ⟨28566472829746643961897787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152354521758648767796788197 28566472829746643961897787)
        ·
          refine ⟨42849709244619965942846681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28566472829746643961897787 42849709244619965942846681)
          ·
            refine ⟨32137281933464974457135011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42849709244619965942846681 32137281933464974457135011)
            ·
              refine ⟨48205922900197461685702517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32137281933464974457135011 48205922900197461685702517)
              ·
                refine ⟨4519305271893512033034611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48205922900197461685702517 4519305271893512033034611)
                ·
                  refine ⟨6778957907840268049551917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519305271893512033034611 6778957907840268049551917)
                  ·
                    refine ⟨2542109215440100518581969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6778957907840268049551917 2542109215440100518581969)
                    ·
                      refine ⟨1906581911580075388936477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542109215440100518581969 1906581911580075388936477)
                      ·
                        rfl

theorem cell23_3713055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_3713055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713055 prefixEnd_3713055 := by exact prefixLift 3713055
  have htrace : WordTrace (prefixWord ++ tailWord_3713055) baseStart_3713055 baseEnd_3713055 := by
    simpa [prefixWord, tailWord_3713055, baseEnd_3713055] using wordTrace_append hprefix tailTrace_3713055
  have hstable : (prefixWord ++ tailWord_3713055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713055).length < 2 ^ (prefixWord ++ tailWord_3713055).sum := by decide
  have hdescent : baseEnd_3713055 < baseStart_3713055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713063 : List Nat := [1, 1, 7, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3713063 : Nat := 118140960795 + 3713063 * 2 ^ 59
def prefixEnd_3713063 : Nat := 4983230072969 + 3 ^ 40 * 3713063 * 2
def baseEnd_3713063 : Nat := 1906586019425311357636441

theorem tailTrace_3713063 : CollatzResearch.WordTrace tailWord_3713063 prefixEnd_3713063 1906586019425311357636441 := by
  unfold tailWord_3713063
  simp only [CollatzResearch.WordTrace]
  refine ⟨135426533347214366518991843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90284355564809577679327895 135426533347214366518991843)
  ·
    refine ⟨203139800020821549778487765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135426533347214366518991843 203139800020821549778487765)
    ·
      refine ⟨4761089062988005072933307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 203139800020821549778487765 4761089062988005072933307)
      ·
        refine ⟨7141633594482007609399961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4761089062988005072933307 7141633594482007609399961)
        ·
          refine ⟨5356225195861505707049971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7141633594482007609399961 5356225195861505707049971)
          ·
            refine ⟨8034337793792258560574957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356225195861505707049971 8034337793792258560574957)
            ·
              refine ⟨3012876672672096960215609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8034337793792258560574957 3012876672672096960215609)
              ·
                refine ⟨2259657504504072720161707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012876672672096960215609 2259657504504072720161707)
                ·
                  refine ⟨3389486256756109080242561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259657504504072720161707 3389486256756109080242561)
                  ·
                    refine ⟨2542114692567081810181921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3389486256756109080242561 2542114692567081810181921)
                    ·
                      refine ⟨1906586019425311357636441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542114692567081810181921 1906586019425311357636441)
                      ·
                        rfl

theorem cell23_3713063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3713063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713063 prefixEnd_3713063 := by exact prefixLift 3713063
  have htrace : WordTrace (prefixWord ++ tailWord_3713063) baseStart_3713063 baseEnd_3713063 := by
    simpa [prefixWord, tailWord_3713063, baseEnd_3713063] using wordTrace_append hprefix tailTrace_3713063
  have hstable : (prefixWord ++ tailWord_3713063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713063).length < 2 ^ (prefixWord ++ tailWord_3713063).sum := by decide
  have hdescent : baseEnd_3713063 < baseStart_3713063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713068 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 5, 4, 2]
def baseStart_3713068 : Nat := 118140960795 + 3713068 * 2 ^ 59
def prefixEnd_3713068 : Nat := 4983230072969 + 3 ^ 40 * 3713068 * 2
def baseEnd_3713068 : Nat := 1906588586828583838073917

theorem tailTrace_3713068 : CollatzResearch.WordTrace tailWord_3713068 prefixEnd_3713068 1906588586828583838073917 := by
  unfold tailWord_3713068
  simp only [CollatzResearch.WordTrace]
  refine ⟨67713357856098126186461929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90284477141464168248615905 67713357856098126186461929)
  ·
    refine ⟨50785018392073594639846447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67713357856098126186461929 50785018392073594639846447)
    ·
      refine ⟨76177527588110391959769671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50785018392073594639846447 76177527588110391959769671)
      ·
        refine ⟨114266291382165587939654507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76177527588110391959769671 114266291382165587939654507)
        ·
          refine ⟨171399437073248381909481761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114266291382165587939654507 171399437073248381909481761)
          ·
            refine ⟨128549577804936286432111321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171399437073248381909481761 128549577804936286432111321)
            ·
              refine ⟨96412183353702214824083491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128549577804936286432111321 96412183353702214824083491)
              ·
                refine ⟨144618275030553322236125237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96412183353702214824083491 144618275030553322236125237)
                ·
                  refine ⟨13557963284114373959636741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144618275030553322236125237 13557963284114373959636741)
                  ·
                    refine ⟨2542118115771445117431889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13557963284114373959636741 2542118115771445117431889)
                    ·
                      refine ⟨1906588586828583838073917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542118115771445117431889 1906588586828583838073917)
                      ·
                        rfl

theorem cell23_3713068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_3713068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713068 prefixEnd_3713068 := by exact prefixLift 3713068
  have htrace : WordTrace (prefixWord ++ tailWord_3713068) baseStart_3713068 baseEnd_3713068 := by
    simpa [prefixWord, tailWord_3713068, baseEnd_3713068] using wordTrace_append hprefix tailTrace_3713068
  have hstable : (prefixWord ++ tailWord_3713068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713068).length < 2 ^ (prefixWord ++ tailWord_3713068).sum := by decide
  have hdescent : baseEnd_3713068 < baseStart_3713068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713078 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3713078 : Nat := 118140960795 + 3713078 * 2 ^ 59
def prefixEnd_3713078 : Nat := 4983230072969 + 3 ^ 40 * 3713078 * 2
def baseEnd_3713078 : Nat := 635531240545042932982957

theorem tailTrace_3713078 : CollatzResearch.WordTrace tailWord_3713078 prefixEnd_3713078 635531240545042932982957 := by
  unfold tailWord_3713078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464192527635001505049243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90284720294773349387191925 8464192527635001505049243)
  ·
    refine ⟨12696288791452502257573865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8464192527635001505049243 12696288791452502257573865)
    ·
      refine ⟨9522216593589376693180399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12696288791452502257573865 9522216593589376693180399)
      ·
        refine ⟨14283324890384065039770599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9522216593589376693180399 14283324890384065039770599)
        ·
          refine ⟨21424987335576097559655899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14283324890384065039770599 21424987335576097559655899)
          ·
            refine ⟨32137481003364146339483849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21424987335576097559655899 32137481003364146339483849)
            ·
              refine ⟨24103110752523109754612887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32137481003364146339483849 24103110752523109754612887)
              ·
                refine ⟨36154666128784664631919331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24103110752523109754612887 36154666128784664631919331)
                ·
                  refine ⟨54231999193176996947878997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36154666128784664631919331 54231999193176996947878997)
                  ·
                    refine ⟨635531240545042932982957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54231999193176996947878997 635531240545042932982957)
                    ·
                      rfl

theorem cell23_3713078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3713078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713078 prefixEnd_3713078 := by exact prefixLift 3713078
  have htrace : WordTrace (prefixWord ++ tailWord_3713078) baseStart_3713078 baseEnd_3713078 := by
    simpa [prefixWord, tailWord_3713078, baseEnd_3713078] using wordTrace_append hprefix tailTrace_3713078
  have hstable : (prefixWord ++ tailWord_3713078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713078).length < 2 ^ (prefixWord ++ tailWord_3713078).sum := by decide
  have hdescent : baseEnd_3713078 < baseStart_3713078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713085 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3713085 : Nat := 118140960795 + 3713085 * 2 ^ 59
def prefixEnd_3713085 : Nat := 4983230072969 + 3 ^ 40 * 3713085 * 2
def baseEnd_3713085 : Nat := 1906597315999710271561339

theorem tailTrace_3713085 : CollatzResearch.WordTrace tailWord_3713085 prefixEnd_3713085 1906597315999710271561339 := by
  unfold tailWord_3713085
  simp only [CollatzResearch.WordTrace]
  refine ⟨135427335753134664276292709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90284890502089776184195139 135427335753134664276292709)
  ·
    refine ⟨25392625453712749551804883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135427335753134664276292709 25392625453712749551804883)
    ·
      refine ⟨38088938180569124327707325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25392625453712749551804883 38088938180569124327707325)
      ·
        refine ⟨14283351817713421622890247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38088938180569124327707325 14283351817713421622890247)
        ·
          refine ⟨21425027726570132434335371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14283351817713421622890247 21425027726570132434335371)
          ·
            refine ⟨32137541589855198651503057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21425027726570132434335371 32137541589855198651503057)
            ·
              refine ⟨24103156192391398988627293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32137541589855198651503057 24103156192391398988627293)
              ·
                refine ⟨9038683572146774620735235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24103156192391398988627293 9038683572146774620735235)
                ·
                  refine ⟨13558025358220161931102853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9038683572146774620735235 13558025358220161931102853)
                  ·
                    refine ⟨2542129754666280362081785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13558025358220161931102853 2542129754666280362081785)
                    ·
                      refine ⟨1906597315999710271561339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542129754666280362081785 1906597315999710271561339)
                      ·
                        rfl

theorem cell23_3713085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3713085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713085 prefixEnd_3713085 := by exact prefixLift 3713085
  have htrace : WordTrace (prefixWord ++ tailWord_3713085) baseStart_3713085 baseEnd_3713085 := by
    simpa [prefixWord, tailWord_3713085, baseEnd_3713085] using wordTrace_append hprefix tailTrace_3713085
  have hstable : (prefixWord ++ tailWord_3713085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713085).length < 2 ^ (prefixWord ++ tailWord_3713085).sum := by decide
  have hdescent : baseEnd_3713085 < baseStart_3713085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713089 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_3713089 : Nat := 118140960795 + 3713089 * 2 ^ 59
def prefixEnd_3713089 : Nat := 4983230072969 + 3 ^ 40 * 3713089 * 2
def baseEnd_3713089 : Nat := 1906599369922328255911321

theorem tailTrace_3713089 : CollatzResearch.WordTrace tailWord_3713089 prefixEnd_3713089 1906599369922328255911321 := by
  unfold tailWord_3713089
  simp only [CollatzResearch.WordTrace]
  refine ⟨135427481645120172959438321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90284987763413448639625547 135427481645120172959438321)
  ·
    refine ⟨101570611233840129719578741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135427481645120172959438321 101570611233840129719578741)
    ·
      refine ⟨9522244803172512161210507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101570611233840129719578741 9522244803172512161210507)
      ·
        refine ⟨14283367204758768241815761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9522244803172512161210507 14283367204758768241815761)
        ·
          refine ⟨10712525403569076181361821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14283367204758768241815761 10712525403569076181361821)
          ·
            refine ⟨4017197026338403568010683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10712525403569076181361821 4017197026338403568010683)
            ·
              refine ⟨6025795539507605352016025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017197026338403568010683 6025795539507605352016025)
              ·
                refine ⟨4519346654630704014012019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025795539507605352016025 4519346654630704014012019)
                ·
                  refine ⟨6779019981946056021018029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519346654630704014012019 6779019981946056021018029)
                  ·
                    refine ⟨2542132493229771007881761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6779019981946056021018029 2542132493229771007881761)
                    ·
                      refine ⟨1906599369922328255911321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542132493229771007881761 1906599369922328255911321)
                      ·
                        rfl

theorem cell23_3713089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_3713089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713089 prefixEnd_3713089 := by exact prefixLift 3713089
  have htrace : WordTrace (prefixWord ++ tailWord_3713089) baseStart_3713089 baseEnd_3713089 := by
    simpa [prefixWord, tailWord_3713089, baseEnd_3713089] using wordTrace_append hprefix tailTrace_3713089
  have hstable : (prefixWord ++ tailWord_3713089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713089).length < 2 ^ (prefixWord ++ tailWord_3713089).sum := by decide
  have hdescent : baseEnd_3713089 < baseStart_3713089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713121 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3713121 : Nat := 118140960795 + 3713121 * 2 ^ 59
def prefixEnd_3713121 : Nat := 4983230072969 + 3 ^ 40 * 3713121 * 2
def baseEnd_3713121 : Nat := 635538600434424043570391

theorem tailTrace_3713121 : CollatzResearch.WordTrace tailWord_3713121 prefixEnd_3713121 635538600434424043570391 := by
  unfold tailWord_3713121
  simp only [CollatzResearch.WordTrace]
  refine ⟨135428648781004242424603217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90285765854002828283068811 135428648781004242424603217)
  ·
    refine ⟨101571486585753181818452413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135428648781004242424603217 101571486585753181818452413)
    ·
      refine ⟨38089307469657443181919655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101571486585753181818452413 38089307469657443181919655)
      ·
        refine ⟨57133961204486164772879483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38089307469657443181919655 57133961204486164772879483)
        ·
          refine ⟨85700941806729247159319225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57133961204486164772879483 85700941806729247159319225)
          ·
            refine ⟨64275706355046935369489419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85700941806729247159319225 64275706355046935369489419)
            ·
              refine ⟨96413559532570403054234129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64275706355046935369489419 96413559532570403054234129)
              ·
                refine ⟨72310169649427802290675597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96413559532570403054234129 72310169649427802290675597)
                ·
                  refine ⟨27116313618535425859003349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72310169649427802290675597 27116313618535425859003349)
                  ·
                    refine ⟨635538600434424043570391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27116313618535425859003349 635538600434424043570391)
                    ·
                      rfl

theorem cell23_3713121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3713121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713121 prefixEnd_3713121 := by exact prefixLift 3713121
  have htrace : WordTrace (prefixWord ++ tailWord_3713121) baseStart_3713121 baseEnd_3713121 := by
    simpa [prefixWord, tailWord_3713121, baseEnd_3713121] using wordTrace_append hprefix tailTrace_3713121
  have hstable : (prefixWord ++ tailWord_3713121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713121).length < 2 ^ (prefixWord ++ tailWord_3713121).sum := by decide
  have hdescent : baseEnd_3713121 < baseStart_3713121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713125 : List Nat := [1, 3, 1, 3, 2, 3, 1, 4, 5]
def baseStart_3713125 : Nat := 118140960795 + 3713125 * 2 ^ 59
def prefixEnd_3713125 : Nat := 4983230072969 + 3 ^ 40 * 3713125 * 2
def baseEnd_3713125 : Nat := 211846428358432235006795

theorem tailTrace_3713125 : CollatzResearch.WordTrace tailWord_3713125 prefixEnd_3713125 211846428358432235006795 := by
  unfold tailWord_3713125
  simp only [CollatzResearch.WordTrace]
  refine ⟨135428794672989751107748829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90285863115326500738499219 135428794672989751107748829)
  ·
    refine ⟨50785798002371156665405811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135428794672989751107748829 50785798002371156665405811)
    ·
      refine ⟨76178697003556734998108717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50785798002371156665405811 76178697003556734998108717)
      ·
        refine ⟨28567011376333775624290769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76178697003556734998108717 28567011376333775624290769)
        ·
          refine ⟨21425258532250331718218077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28567011376333775624290769 21425258532250331718218077)
          ·
            refine ⟨8034471949593874394331779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21425258532250331718218077 8034471949593874394331779)
            ·
              refine ⟨12051707924390811591497669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8034471949593874394331779 12051707924390811591497669)
              ·
                refine ⟨2259695235823277173405813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12051707924390811591497669 2259695235823277173405813)
                ·
                  refine ⟨211846428358432235006795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2259695235823277173405813 211846428358432235006795)
                  ·
                    rfl

theorem cell23_3713125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_3713125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713125 prefixEnd_3713125 := by exact prefixLift 3713125
  have htrace : WordTrace (prefixWord ++ tailWord_3713125) baseStart_3713125 baseEnd_3713125 := by
    simpa [prefixWord, tailWord_3713125, baseEnd_3713125] using wordTrace_append hprefix tailTrace_3713125
  have hstable : (prefixWord ++ tailWord_3713125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713125).length < 2 ^ (prefixWord ++ tailWord_3713125).sum := by decide
  have hdescent : baseEnd_3713125 < baseStart_3713125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713155 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 2, 5]
def baseStart_3713155 : Nat := 118140960795 + 3713155 * 2 ^ 59
def prefixEnd_3713155 : Nat := 4983230072969 + 3 ^ 40 * 3713155 * 2
def baseEnd_3713155 : Nat := 635544419881841665895339

theorem tailTrace_3713155 : CollatzResearch.WordTrace tailWord_3713155 prefixEnd_3713155 635544419881841665895339 := by
  unfold tailWord_3713155
  simp only [CollatzResearch.WordTrace]
  refine ⟨135429888862881066231340919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90286592575254044154227279 135429888862881066231340919)
  ·
    refine ⟨203144833294321599347011379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135429888862881066231340919 203144833294321599347011379)
    ·
      refine ⟨304717249941482399020517069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203144833294321599347011379 304717249941482399020517069)
      ·
        refine ⟨114268968728055899632693901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304717249941482399020517069 114268968728055899632693901)
        ·
          refine ⟨42850863273020962362260213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114268968728055899632693901 42850863273020962362260213)
          ·
            refine ⟨4017268431845715221461895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42850863273020962362260213 4017268431845715221461895)
            ·
              refine ⟨6025902647768572832192843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017268431845715221461895 6025902647768572832192843)
              ·
                refine ⟨9038853971652859248289265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025902647768572832192843 9038853971652859248289265)
                ·
                  refine ⟨6779140478739644436216949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9038853971652859248289265 6779140478739644436216949)
                  ·
                    refine ⟨635544419881841665895339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6779140478739644436216949 635544419881841665895339)
                    ·
                      rfl

theorem cell23_3713155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 5].length) (baseStart_3713155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713155 prefixEnd_3713155 := by exact prefixLift 3713155
  have htrace : WordTrace (prefixWord ++ tailWord_3713155) baseStart_3713155 baseEnd_3713155 := by
    simpa [prefixWord, tailWord_3713155, baseEnd_3713155] using wordTrace_append hprefix tailTrace_3713155
  have hstable : (prefixWord ++ tailWord_3713155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713155).length < 2 ^ (prefixWord ++ tailWord_3713155).sum := by decide
  have hdescent : baseEnd_3713155 < baseStart_3713155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713168 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 5, 4]
def baseStart_3713168 : Nat := 118140960795 + 3713168 * 2 ^ 59
def prefixEnd_3713168 : Nat := 4983230072969 + 3 ^ 40 * 3713168 * 2
def baseEnd_3713168 : Nat := 635546644964677815607819

theorem tailTrace_3713168 : CollatzResearch.WordTrace tailWord_3713168 prefixEnd_3713168 635546644964677815607819 := by
  unfold tailWord_3713168
  simp only [CollatzResearch.WordTrace]
  refine ⟨67715181505916984725782079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90286908674555979634376105 67715181505916984725782079)
  ·
    refine ⟨101572772258875477088673119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67715181505916984725782079 101572772258875477088673119)
    ·
      refine ⟨152359158388313215633009679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101572772258875477088673119 152359158388313215633009679)
      ·
        refine ⟨228538737582469823449514519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152359158388313215633009679 228538737582469823449514519)
        ·
          refine ⟨342808106373704735174271779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228538737582469823449514519 342808106373704735174271779)
          ·
            refine ⟨514212159560557102761407669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342808106373704735174271779 514212159560557102761407669)
            ·
              refine ⟨48207389958802228383881969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 514212159560557102761407669 48207389958802228383881969)
              ·
                refine ⟨36155542469101671287911477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48207389958802228383881969 36155542469101671287911477)
                ·
                  refine ⟨3389582106478281683241701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36155542469101671287911477 3389582106478281683241701)
                  ·
                    refine ⟨635546644964677815607819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389582106478281683241701 635546644964677815607819)
                    ·
                      rfl

theorem cell23_3713168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_3713168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713168 prefixEnd_3713168 := by exact prefixLift 3713168
  have htrace : WordTrace (prefixWord ++ tailWord_3713168) baseStart_3713168 baseEnd_3713168 := by
    simpa [prefixWord, tailWord_3713168, baseEnd_3713168] using wordTrace_append hprefix tailTrace_3713168
  have hstable : (prefixWord ++ tailWord_3713168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713168).length < 2 ^ (prefixWord ++ tailWord_3713168).sum := by decide
  have hdescent : baseEnd_3713168 < baseStart_3713168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713185 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 3, 4]
def baseStart_3713185 : Nat := 118140960795 + 3713185 * 2 ^ 59
def prefixEnd_3713185 : Nat := 4983230072969 + 3 ^ 40 * 3713185 * 2
def baseEnd_3713185 : Nat := 635549554688386626770293

theorem tailTrace_3713185 : CollatzResearch.WordTrace tailWord_3713185 prefixEnd_3713185 635549554688386626770293 := by
  unfold tailWord_3713185
  simp only [CollatzResearch.WordTrace]
  refine ⟨135430983052772381354933009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90287322035181587569955339 135430983052772381354933009)
  ·
    refine ⟨101573237289579286016199757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135430983052772381354933009 101573237289579286016199757)
    ·
      refine ⟨38089963983592232256074909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101573237289579286016199757 38089963983592232256074909)
      ·
        refine ⟨14283736493847087096028091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38089963983592232256074909 14283736493847087096028091)
        ·
          refine ⟨21425604740770630644042137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14283736493847087096028091 21425604740770630644042137)
          ·
            refine ⟨16069203555577972983031603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21425604740770630644042137 16069203555577972983031603)
            ·
              refine ⟨24103805333366959474547405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16069203555577972983031603 24103805333366959474547405)
              ·
                refine ⟨9038927000012609802955277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24103805333366959474547405 9038927000012609802955277)
                ·
                  refine ⟨3389597625004728676108229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9038927000012609802955277 3389597625004728676108229)
                  ·
                    refine ⟨635549554688386626770293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389597625004728676108229 635549554688386626770293)
                    ·
                      rfl

theorem cell23_3713185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_3713185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713185 prefixEnd_3713185 := by exact prefixLift 3713185
  have htrace : WordTrace (prefixWord ++ tailWord_3713185) baseStart_3713185 baseEnd_3713185 := by
    simpa [prefixWord, tailWord_3713185, baseEnd_3713185] using wordTrace_append hprefix tailTrace_3713185
  have hstable : (prefixWord ++ tailWord_3713185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713185).length < 2 ^ (prefixWord ++ tailWord_3713185).sum := by decide
  have hdescent : baseEnd_3713185 < baseStart_3713185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713208 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_3713208 : Nat := 118140960795 + 3713208 * 2 ^ 59
def prefixEnd_3713208 : Nat := 4983230072969 + 3 ^ 40 * 3713208 * 2
def baseEnd_3713208 : Nat := 1906660474120213290323273

theorem tailTrace_3713208 : CollatzResearch.WordTrace tailWord_3713208 prefixEnd_3713208 1906660474120213290323273 := by
  unfold tailWord_3713208
  simp only [CollatzResearch.WordTrace]
  refine ⟨67715910965844528141510139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90287881287792704188680185 67715910965844528141510139)
  ·
    refine ⟨101573866448766792212265209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67715910965844528141510139 101573866448766792212265209)
    ·
      refine ⟨76180399836575094159198907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101573866448766792212265209 76180399836575094159198907)
      ·
        refine ⟨114270599754862641238798361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76180399836575094159198907 114270599754862641238798361)
        ·
          refine ⟨85702949816146980929098771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114270599754862641238798361 85702949816146980929098771)
          ·
            refine ⟨128554424724220471393648157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85702949816146980929098771 128554424724220471393648157)
            ·
              refine ⟨48207909271582676772618059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128554424724220471393648157 48207909271582676772618059)
              ·
                refine ⟨72311863907374015158927089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48207909271582676772618059 72311863907374015158927089)
                ·
                  refine ⟨54233897930530511369195317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72311863907374015158927089 54233897930530511369195317)
                  ·
                    refine ⟨5084427930987235440862061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54233897930530511369195317 5084427930987235440862061)
                    ·
                      refine ⟨1906660474120213290323273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084427930987235440862061 1906660474120213290323273)
                      ·
                        rfl

theorem cell23_3713208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_3713208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713208 prefixEnd_3713208 := by exact prefixLift 3713208
  have htrace : WordTrace (prefixWord ++ tailWord_3713208) baseStart_3713208 baseEnd_3713208 := by
    simpa [prefixWord, tailWord_3713208, baseEnd_3713208] using wordTrace_append hprefix tailTrace_3713208
  have hstable : (prefixWord ++ tailWord_3713208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713208).length < 2 ^ (prefixWord ++ tailWord_3713208).sum := by decide
  have hdescent : baseEnd_3713208 < baseStart_3713208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713242 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_3713242 : Nat := 118140960795 + 3713242 * 2 ^ 59
def prefixEnd_3713242 : Nat := 4983230072969 + 3 ^ 40 * 3713242 * 2
def baseEnd_3713242 : Nat := 1906677932462466157298117

theorem tailTrace_3713242 : CollatzResearch.WordTrace tailWord_3713242 prefixEnd_3713242 1906677932462466157298117 := by
  unfold tailWord_3713242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33858265503391470022439495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90288708009043920059838653 33858265503391470022439495)
  ·
    refine ⟨50787398255087205033659243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33858265503391470022439495 50787398255087205033659243)
    ·
      refine ⟨76181097382630807550488865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50787398255087205033659243 76181097382630807550488865)
      ·
        refine ⟨57135823036973105662866649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76181097382630807550488865 57135823036973105662866649)
        ·
          refine ⟨42851867277729829247149987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57135823036973105662866649 42851867277729829247149987)
          ·
            refine ⟨64277800916594743870724981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42851867277729829247149987 64277800916594743870724981)
            ·
              refine ⟨6026043835930757237880467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64277800916594743870724981 6026043835930757237880467)
              ·
                refine ⟨9039065753896135856820701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026043835930757237880467 9039065753896135856820701)
                ·
                  refine ⟨3389649657711050946307763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9039065753896135856820701 3389649657711050946307763)
                  ·
                    refine ⟨5084474486566576419461645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389649657711050946307763 5084474486566576419461645)
                    ·
                      refine ⟨1906677932462466157298117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084474486566576419461645 1906677932462466157298117)
                      ·
                        rfl

theorem cell23_3713242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_3713242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713242 prefixEnd_3713242 := by exact prefixLift 3713242
  have htrace : WordTrace (prefixWord ++ tailWord_3713242) baseStart_3713242 baseEnd_3713242 := by
    simpa [prefixWord, tailWord_3713242, baseEnd_3713242] using wordTrace_append hprefix tailTrace_3713242
  have hstable : (prefixWord ++ tailWord_3713242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713242).length < 2 ^ (prefixWord ++ tailWord_3713242).sum := by decide
  have hdescent : baseEnd_3713242 < baseStart_3713242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713265 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 2, 6, 2]
def baseStart_3713265 : Nat := 118140960795 + 3713265 * 2 ^ 59
def prefixEnd_3713265 : Nat := 4983230072969 + 3 ^ 40 * 3713265 * 2
def baseEnd_3713265 : Nat := 1906689742517519567310511

theorem tailTrace_3713265 : CollatzResearch.WordTrace tailWord_3713265 prefixEnd_3713265 1906689742517519567310511 := by
  unfold tailWord_3713265
  simp only [CollatzResearch.WordTrace]
  refine ⟨135433900892482555017845249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90289267261655036678563499 135433900892482555017845249)
  ·
    refine ⟨101575425669361916263383937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135433900892482555017845249 101575425669361916263383937)
    ·
      refine ⟨76181569252021437197537953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101575425669361916263383937 76181569252021437197537953)
      ·
        refine ⟨57136176939016077898153465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76181569252021437197537953 57136176939016077898153465)
        ·
          refine ⟨42852132704262058423615099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57136176939016077898153465 42852132704262058423615099)
          ·
            refine ⟨64278199056393087635422649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42852132704262058423615099 64278199056393087635422649)
            ·
              refine ⟨48208649292294815726566987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64278199056393087635422649 48208649292294815726566987)
              ·
                refine ⟨72312973938442223589850481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48208649292294815726566987 72312973938442223589850481)
                ·
                  refine ⟨54234730453831667692387861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72312973938442223589850481 54234730453831667692387861)
                  ·
                    refine ⟨2542252990023359423080681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54234730453831667692387861 2542252990023359423080681)
                    ·
                      refine ⟨1906689742517519567310511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542252990023359423080681 1906689742517519567310511)
                      ·
                        rfl

theorem cell23_3713265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_3713265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713265 prefixEnd_3713265 := by exact prefixLift 3713265
  have htrace : WordTrace (prefixWord ++ tailWord_3713265) baseStart_3713265 baseEnd_3713265 := by
    simpa [prefixWord, tailWord_3713265, baseEnd_3713265] using wordTrace_append hprefix tailTrace_3713265
  have hstable : (prefixWord ++ tailWord_3713265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713265).length < 2 ^ (prefixWord ++ tailWord_3713265).sum := by decide
  have hdescent : baseEnd_3713265 < baseStart_3713265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713288 : List Nat := [2, 1, 3, 2, 3, 12]
def baseStart_3713288 : Nat := 118140960795 + 3713288 * 2 ^ 59
def prefixEnd_3713288 : Nat := 4983230072969 + 3 ^ 40 * 3713288 * 2
def baseEnd_3713288 : Nat := 7846508446800711840835

theorem tailTrace_3713288 : CollatzResearch.WordTrace tailWord_3713288 prefixEnd_3713288 7846508446800711840835 := by
  unfold tailWord_3713288
  simp only [CollatzResearch.WordTrace]
  refine ⟨67717369885699614972966259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90289826514266153297288345 67717369885699614972966259)
  ·
    refine ⟨101576054828549422459449389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67717369885699614972966259 101576054828549422459449389)
    ·
      refine ⟨38091020560706033422293521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101576054828549422459449389 38091020560706033422293521)
      ·
        refine ⟨28568265420529525066720141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38091020560706033422293521 28568265420529525066720141)
        ·
          refine ⟨10713099532698571900020053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28568265420529525066720141 10713099532698571900020053)
          ·
            refine ⟨7846508446800711840835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10713099532698571900020053 7846508446800711840835)
            ·
              rfl

theorem cell23_3713288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 12].length) (baseStart_3713288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713288 prefixEnd_3713288 := by exact prefixLift 3713288
  have htrace : WordTrace (prefixWord ++ tailWord_3713288) baseStart_3713288 baseEnd_3713288 := by
    simpa [prefixWord, tailWord_3713288, baseEnd_3713288] using wordTrace_append hprefix tailTrace_3713288
  have hstable : (prefixWord ++ tailWord_3713288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713288).length < 2 ^ (prefixWord ++ tailWord_3713288).sum := by decide
  have hdescent : baseEnd_3713288 < baseStart_3713288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713292 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_3713292 : Nat := 118140960795 + 3713292 * 2 ^ 59
def prefixEnd_3713292 : Nat := 4983230072969 + 3 ^ 40 * 3713292 * 2
def baseEnd_3713292 : Nat := 635567868831730320557629

theorem tailTrace_3713292 : CollatzResearch.WordTrace tailWord_3713292 prefixEnd_3713292 635567868831730320557629 := by
  unfold tailWord_3713292
  simp only [CollatzResearch.WordTrace]
  refine ⟨67717442831692369314539065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90289923775589825752718753 67717442831692369314539065)
  ·
    refine ⟨50788082123769276985904299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67717442831692369314539065 50788082123769276985904299)
    ·
      refine ⟨76182123185653915478856449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50788082123769276985904299 76182123185653915478856449)
      ·
        refine ⟨57136592389240436609142337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76182123185653915478856449 57136592389240436609142337)
        ·
          refine ⟨42852444291930327456856753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57136592389240436609142337 42852444291930327456856753)
          ·
            refine ⟨32139333218947745592642565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42852444291930327456856753 32139333218947745592642565)
            ·
              refine ⟨6026124978552702298620481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32139333218947745592642565 6026124978552702298620481)
              ·
                refine ⟨4519593733914526723965361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6026124978552702298620481 4519593733914526723965361)
                ·
                  refine ⟨3389695300435895042974021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4519593733914526723965361 3389695300435895042974021)
                  ·
                    refine ⟨635567868831730320557629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389695300435895042974021 635567868831730320557629)
                    ·
                      rfl

theorem cell23_3713292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_3713292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713292 prefixEnd_3713292 := by exact prefixLift 3713292
  have htrace : WordTrace (prefixWord ++ tailWord_3713292) baseStart_3713292 baseEnd_3713292 := by
    simpa [prefixWord, tailWord_3713292, baseEnd_3713292] using wordTrace_append hprefix tailTrace_3713292
  have hstable : (prefixWord ++ tailWord_3713292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713292).length < 2 ^ (prefixWord ++ tailWord_3713292).sum := by decide
  have hdescent : baseEnd_3713292 < baseStart_3713292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713312 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3713312 : Nat := 118140960795 + 3713312 * 2 ^ 59
def prefixEnd_3713312 : Nat := 4983230072969 + 3 ^ 40 * 3713312 * 2
def baseEnd_3713312 : Nat := 1906713876108280883422795

theorem tailTrace_3713312 : CollatzResearch.WordTrace tailWord_3713312 prefixEnd_3713312 1906713876108280883422795 := by
  unfold tailWord_3713312
  simp only [CollatzResearch.WordTrace]
  refine ⟨67717807561656141022403095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90290410082208188029870793 67717807561656141022403095)
  ·
    refine ⟨101576711342484211533604643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67717807561656141022403095 101576711342484211533604643)
    ·
      refine ⟨152365067013726317300406965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101576711342484211533604643 152365067013726317300406965)
      ·
        refine ⟨14284225032536842246913153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152365067013726317300406965 14284225032536842246913153)
        ·
          refine ⟨10713168774402631685184865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14284225032536842246913153 10713168774402631685184865)
          ·
            refine ⟨8034876580801973763888649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10713168774402631685184865 8034876580801973763888649)
            ·
              refine ⟨6026157435601480322916487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034876580801973763888649 6026157435601480322916487)
              ·
                refine ⟨9039236153402220484374731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026157435601480322916487 9039236153402220484374731)
                ·
                  refine ⟨13558854230103330726562097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9039236153402220484374731 13558854230103330726562097)
                  ·
                    refine ⟨10169140672577498044921573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13558854230103330726562097 10169140672577498044921573)
                    ·
                      refine ⟨1906713876108280883422795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10169140672577498044921573 1906713876108280883422795)
                      ·
                        rfl

theorem cell23_3713312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3713312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713312 prefixEnd_3713312 := by exact prefixLift 3713312
  have htrace : WordTrace (prefixWord ++ tailWord_3713312) baseStart_3713312 baseEnd_3713312 := by
    simpa [prefixWord, tailWord_3713312, baseEnd_3713312] using wordTrace_append hprefix tailTrace_3713312
  have hstable : (prefixWord ++ tailWord_3713312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713312).length < 2 ^ (prefixWord ++ tailWord_3713312).sum := by decide
  have hdescent : baseEnd_3713312 < baseStart_3713312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713375 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 3]
def baseStart_3713375 : Nat := 118140960795 + 3713375 * 2 ^ 59
def prefixEnd_3713375 : Nat := 4983230072969 + 3 ^ 40 * 3713375 * 2
def baseEnd_3713375 : Nat := 1906746225389514136935005

theorem tailTrace_3713375 : CollatzResearch.WordTrace tailWord_3713375 prefixEnd_3713375 1906746225389514136935005 := by
  unfold tailWord_3713375
  simp only [CollatzResearch.WordTrace]
  refine ⟨135437912922084043804349579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90291941948056029202899719 135437912922084043804349579)
  ·
    refine ⟨203156869383126065706524369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135437912922084043804349579 203156869383126065706524369)
    ·
      refine ⟨152367652037344549279893277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203156869383126065706524369 152367652037344549279893277)
      ·
        refine ⟨57137869514004205979959979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152367652037344549279893277 57137869514004205979959979)
        ·
          refine ⟨85706804271006308969939969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57137869514004205979959979 85706804271006308969939969)
          ·
            refine ⟨64280103203254731727454977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85706804271006308969939969 64280103203254731727454977)
            ·
              refine ⟨48210077402441048795591233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64280103203254731727454977 48210077402441048795591233)
              ·
                refine ⟨36157558051830786596693425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48210077402441048795591233 36157558051830786596693425)
                ·
                  refine ⟨27118168538873089947520069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36157558051830786596693425 27118168538873089947520069)
                  ·
                    refine ⟨5084656601038704365160013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27118168538873089947520069 5084656601038704365160013)
                    ·
                      refine ⟨1906746225389514136935005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084656601038704365160013 1906746225389514136935005)
                      ·
                        rfl

theorem cell23_3713375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_3713375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713375 prefixEnd_3713375 := by exact prefixLift 3713375
  have htrace : WordTrace (prefixWord ++ tailWord_3713375) baseStart_3713375 baseEnd_3713375 := by
    simpa [prefixWord, tailWord_3713375, baseEnd_3713375] using wordTrace_append hprefix tailTrace_3713375
  have hstable : (prefixWord ++ tailWord_3713375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713375).length < 2 ^ (prefixWord ++ tailWord_3713375).sum := by decide
  have hdescent : baseEnd_3713375 < baseStart_3713375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713376 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 1, 3, 2]
def baseStart_3713376 : Nat := 118140960795 + 3713376 * 2 ^ 59
def prefixEnd_3713376 : Nat := 4983230072969 + 3 ^ 40 * 3713376 * 2
def baseEnd_3713376 : Nat := 1906746738870168633022501

theorem tailTrace_3713376 : CollatzResearch.WordTrace tailWord_3713376 prefixEnd_3713376 1906746738870168633022501 := by
  unfold tailWord_3713376
  simp only [CollatzResearch.WordTrace]
  refine ⟨67718974697540210487567991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90291966263386947316757321 67718974697540210487567991)
  ·
    refine ⟨101578462046310315731351987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67718974697540210487567991 101578462046310315731351987)
    ·
      refine ⟨152367693069465473597027981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101578462046310315731351987 152367693069465473597027981)
      ·
        refine ⟨57137884901049552598885493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152367693069465473597027981 57137884901049552598885493)
        ·
          refine ⟨5356676709473395556145515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57137884901049552598885493 5356676709473395556145515)
          ·
            refine ⟨8035015064210093334218273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356676709473395556145515 8035015064210093334218273)
            ·
              refine ⟨6026261298157570000663705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8035015064210093334218273 6026261298157570000663705)
              ·
                refine ⟨4519695973618177500497779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6026261298157570000663705 4519695973618177500497779)
                ·
                  refine ⟨6779543960427266250746669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519695973618177500497779 6779543960427266250746669)
                  ·
                    refine ⟨2542328985160224844030001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6779543960427266250746669 2542328985160224844030001)
                    ·
                      refine ⟨1906746738870168633022501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542328985160224844030001 1906746738870168633022501)
                      ·
                        rfl

theorem cell23_3713376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_3713376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713376 prefixEnd_3713376 := by exact prefixLift 3713376
  have htrace : WordTrace (prefixWord ++ tailWord_3713376) baseStart_3713376 baseEnd_3713376 := by
    simpa [prefixWord, tailWord_3713376, baseEnd_3713376] using wordTrace_append hprefix tailTrace_3713376
  have hstable : (prefixWord ++ tailWord_3713376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713376).length < 2 ^ (prefixWord ++ tailWord_3713376).sum := by decide
  have hdescent : baseEnd_3713376 < baseStart_3713376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713389 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_3713389 : Nat := 118140960795 + 3713389 * 2 ^ 59
def prefixEnd_3713389 : Nat := 4983230072969 + 3 ^ 40 * 3713389 * 2
def baseEnd_3713389 : Nat := 1906753414118677082159941

theorem tailTrace_3713389 : CollatzResearch.WordTrace tailWord_3713389 prefixEnd_3713389 1906753414118677082159941 := by
  unfold tailWord_3713389
  simp only [CollatzResearch.WordTrace]
  refine ⟨135438423544033324195359221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90292282362688882796906147 135438423544033324195359221)
  ·
    refine ⟨12697352207253124143314927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135438423544033324195359221 12697352207253124143314927)
    ·
      refine ⟨19046028310879686214972391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12697352207253124143314927 19046028310879686214972391)
      ·
        refine ⟨28569042466319529322458587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19046028310879686214972391 28569042466319529322458587)
        ·
          refine ⟨42853563699479293983687881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28569042466319529322458587 42853563699479293983687881)
          ·
            refine ⟨32140172774609470487765911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42853563699479293983687881 32140172774609470487765911)
            ·
              refine ⟨48210259161914205731648867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32140172774609470487765911 48210259161914205731648867)
              ·
                refine ⟨72315388742871308597473301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48210259161914205731648867 72315388742871308597473301)
                ·
                  refine ⟨3389783847322092590506561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72315388742871308597473301 3389783847322092590506561)
                  ·
                    refine ⟨2542337885491569442879921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3389783847322092590506561 2542337885491569442879921)
                    ·
                      refine ⟨1906753414118677082159941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542337885491569442879921 1906753414118677082159941)
                      ·
                        rfl

theorem cell23_3713389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_3713389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713389 prefixEnd_3713389 := by exact prefixLift 3713389
  have htrace : WordTrace (prefixWord ++ tailWord_3713389) baseStart_3713389 baseEnd_3713389 := by
    simpa [prefixWord, tailWord_3713389, baseEnd_3713389] using wordTrace_append hprefix tailTrace_3713389
  have hstable : (prefixWord ++ tailWord_3713389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713389).length < 2 ^ (prefixWord ++ tailWord_3713389).sum := by decide
  have hdescent : baseEnd_3713389 < baseStart_3713389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713472 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 3, 4]
def baseStart_3713472 : Nat := 118140960795 + 3713472 * 2 ^ 59
def prefixEnd_3713472 : Nat := 4983230072969 + 3 ^ 40 * 3713472 * 2
def baseEnd_3713472 : Nat := 635598677671000085807353

theorem tailTrace_3713472 : CollatzResearch.WordTrace tailWord_3713472 prefixEnd_3713472 635598677671000085807353 := by
  unfold tailWord_3713472
  simp only [CollatzResearch.WordTrace]
  refine ⟨67720725401366314685315335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90294300535155086247087113 67720725401366314685315335)
  ·
    refine ⟨101581088102049472027973003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67720725401366314685315335 101581088102049472027973003)
    ·
      refine ⟨152371632153074208041959505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101581088102049472027973003 152371632153074208041959505)
      ·
        refine ⟨114278724114805656031469629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152371632153074208041959505 114278724114805656031469629)
        ·
          refine ⟨42854521543052121011801111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114278724114805656031469629 42854521543052121011801111)
          ·
            refine ⟨64281782314578181517701667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42854521543052121011801111 64281782314578181517701667)
            ·
              refine ⟨96422673471867272276552501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64281782314578181517701667 96422673471867272276552501)
              ·
                refine ⟨9039625637987556775926797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96422673471867272276552501 9039625637987556775926797)
                ·
                  refine ⟨3389859614245333790972549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9039625637987556775926797 3389859614245333790972549)
                  ·
                    refine ⟨635598677671000085807353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389859614245333790972549 635598677671000085807353)
                    ·
                      rfl

theorem cell23_3713472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_3713472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713472 prefixEnd_3713472 := by exact prefixLift 3713472
  have htrace : WordTrace (prefixWord ++ tailWord_3713472) baseStart_3713472 baseEnd_3713472 := by
    simpa [prefixWord, tailWord_3713472, baseEnd_3713472] using wordTrace_append hprefix tailTrace_3713472
  have hstable : (prefixWord ++ tailWord_3713472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713472).length < 2 ^ (prefixWord ++ tailWord_3713472).sum := by decide
  have hdescent : baseEnd_3713472 < baseStart_3713472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713473 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3713473 : Nat := 118140960795 + 3713473 * 2 ^ 59
def prefixEnd_3713473 : Nat := 4983230072969 + 3 ^ 40 * 3713473 * 2
def baseEnd_3713473 : Nat := 1906796546493654753509555

theorem tailTrace_3713473 : CollatzResearch.WordTrace tailWord_3713473 prefixEnd_3713473 1906796546493654753509555 := by
  unfold tailWord_3713473
  simp only [CollatzResearch.WordTrace]
  refine ⟨135441487275729006541417073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90294324850486004360944715 135441487275729006541417073)
  ·
    refine ⟨101581115456796754906062805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135441487275729006541417073 101581115456796754906062805)
    ·
      refine ⟨2380807393518673943110847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101581115456796754906062805 2380807393518673943110847)
      ·
        refine ⟨3571211090278010914666271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380807393518673943110847 3571211090278010914666271)
        ·
          refine ⟨5356816635417016371999407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571211090278010914666271 5356816635417016371999407)
          ·
            refine ⟨8035224953125524557999111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356816635417016371999407 8035224953125524557999111)
            ·
              refine ⟨12052837429688286836998667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035224953125524557999111 12052837429688286836998667)
              ·
                refine ⟨18079256144532430255498001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12052837429688286836998667 18079256144532430255498001)
                ·
                  refine ⟨13559442108399322691623501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18079256144532430255498001 13559442108399322691623501)
                  ·
                    refine ⟨5084790790649746009358813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13559442108399322691623501 5084790790649746009358813)
                    ·
                      refine ⟨1906796546493654753509555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084790790649746009358813 1906796546493654753509555)
                      ·
                        rfl

theorem cell23_3713473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3713473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713473 prefixEnd_3713473 := by exact prefixLift 3713473
  have htrace : WordTrace (prefixWord ++ tailWord_3713473) baseStart_3713473 baseEnd_3713473 := by
    simpa [prefixWord, tailWord_3713473, baseEnd_3713473] using wordTrace_append hprefix tailTrace_3713473
  have hstable : (prefixWord ++ tailWord_3713473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713473).length < 2 ^ (prefixWord ++ tailWord_3713473).sum := by decide
  have hdescent : baseEnd_3713473 < baseStart_3713473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713475 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4]
def baseStart_3713475 : Nat := 118140960795 + 3713475 * 2 ^ 59
def prefixEnd_3713475 : Nat := 4983230072969 + 3 ^ 40 * 3713475 * 2
def baseEnd_3713475 : Nat := 1906797573454963745684545

theorem tailTrace_3713475 : CollatzResearch.WordTrace tailWord_3713475 prefixEnd_3713475 1906797573454963745684545 := by
  unfold tailWord_3713475
  simp only [CollatzResearch.WordTrace]
  refine ⟨135441560221721760882989879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90294373481147840588659919 135441560221721760882989879)
  ·
    refine ⟨203162340332582641324484819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135441560221721760882989879 203162340332582641324484819)
    ·
      refine ⟨304743510498873961986727229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203162340332582641324484819 304743510498873961986727229)
      ·
        refine ⟨114278816437077735745022711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304743510498873961986727229 114278816437077735745022711)
        ·
          refine ⟨171418224655616603617534067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114278816437077735745022711 171418224655616603617534067)
          ·
            refine ⟨257127336983424905426301101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171418224655616603617534067 257127336983424905426301101)
            ·
              refine ⟨96422751368784339534862913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257127336983424905426301101 96422751368784339534862913)
              ·
                refine ⟨72317063526588254651147185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96422751368784339534862913 72317063526588254651147185)
                ·
                  refine ⟨54237797644941190988360389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72317063526588254651147185 54237797644941190988360389)
                  ·
                    refine ⟨10169587058426473310317573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54237797644941190988360389 10169587058426473310317573)
                    ·
                      refine ⟨1906797573454963745684545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10169587058426473310317573 1906797573454963745684545)
                      ·
                        rfl

theorem cell23_3713475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_3713475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713475 prefixEnd_3713475 := by exact prefixLift 3713475
  have htrace : WordTrace (prefixWord ++ tailWord_3713475) baseStart_3713475 baseEnd_3713475 := by
    simpa [prefixWord, tailWord_3713475, baseEnd_3713475] using wordTrace_append hprefix tailTrace_3713475
  have hstable : (prefixWord ++ tailWord_3713475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713475).length < 2 ^ (prefixWord ++ tailWord_3713475).sum := by decide
  have hdescent : baseEnd_3713475 < baseStart_3713475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713479 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_3713479 : Nat := 118140960795 + 3713479 * 2 ^ 59
def prefixEnd_3713479 : Nat := 4983230072969 + 3 ^ 40 * 3713479 * 2
def baseEnd_3713479 : Nat := 1906799627377581730034527

theorem tailTrace_3713479 : CollatzResearch.WordTrace tailWord_3713479 prefixEnd_3713479 1906799627377581730034527 := by
  unfold tailWord_3713479
  simp only [CollatzResearch.WordTrace]
  refine ⟨135441706113707269566135491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90294470742471513044090327 135441706113707269566135491)
  ·
    refine ⟨203162559170560904349203237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135441706113707269566135491 203162559170560904349203237)
    ·
      refine ⟨38092979844480169565475607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203162559170560904349203237 38092979844480169565475607)
      ·
        refine ⟨57139469766720254348213411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38092979844480169565475607 57139469766720254348213411)
        ·
          refine ⟨85709204650080381522320117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57139469766720254348213411 85709204650080381522320117)
          ·
            refine ⟨8035237935945035767717511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85709204650080381522320117 8035237935945035767717511)
            ·
              refine ⟨12052856903917553651576267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035237935945035767717511 12052856903917553651576267)
              ·
                refine ⟨18079285355876330477364401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12052856903917553651576267 18079285355876330477364401)
                ·
                  refine ⟨13559464016907247858023301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18079285355876330477364401 13559464016907247858023301)
                  ·
                    refine ⟨2542399503170108973379369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13559464016907247858023301 2542399503170108973379369)
                    ·
                      refine ⟨1906799627377581730034527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542399503170108973379369 1906799627377581730034527)
                      ·
                        rfl

theorem cell23_3713479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_3713479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713479 prefixEnd_3713479 := by exact prefixLift 3713479
  have htrace : WordTrace (prefixWord ++ tailWord_3713479) baseStart_3713479 baseEnd_3713479 := by
    simpa [prefixWord, tailWord_3713479, baseEnd_3713479] using wordTrace_append hprefix tailTrace_3713479
  have hstable : (prefixWord ++ tailWord_3713479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713479).length < 2 ^ (prefixWord ++ tailWord_3713479).sum := by decide
  have hdescent : baseEnd_3713479 < baseStart_3713479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713482 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_3713482 : Nat := 118140960795 + 3713482 * 2 ^ 59
def prefixEnd_3713482 : Nat := 4983230072969 + 3 ^ 40 * 3713482 * 2
def baseEnd_3713482 : Nat := 1906801167819545218297013

theorem tailTrace_3713482 : CollatzResearch.WordTrace tailWord_3713482 prefixEnd_3713482 1906801167819545218297013 := by
  unfold tailWord_3713482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33860453883174100269623675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90294543688464267385663133 33860453883174100269623675)
  ·
    refine ⟨50790680824761150404435513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33860453883174100269623675 50790680824761150404435513)
    ·
      refine ⟨38093010618570862803326635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50790680824761150404435513 38093010618570862803326635)
      ·
        refine ⟨57139515927856294204989953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38093010618570862803326635 57139515927856294204989953)
        ·
          refine ⟨42854636945892220653742465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57139515927856294204989953 42854636945892220653742465)
          ·
            refine ⟨32140977709419165490306849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42854636945892220653742465 32140977709419165490306849)
            ·
              refine ⟨24105733282064374117730137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32140977709419165490306849 24105733282064374117730137)
              ·
                refine ⟨18079299961548280588297603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24105733282064374117730137 18079299961548280588297603)
                ·
                  refine ⟨27118949942322420882446405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18079299961548280588297603 27118949942322420882446405)
                  ·
                    refine ⟨5084803114185453915458701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27118949942322420882446405 5084803114185453915458701)
                    ·
                      refine ⟨1906801167819545218297013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084803114185453915458701 1906801167819545218297013)
                      ·
                        rfl

theorem cell23_3713482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_3713482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713482 prefixEnd_3713482 := by exact prefixLift 3713482
  have htrace : WordTrace (prefixWord ++ tailWord_3713482) baseStart_3713482 baseEnd_3713482 := by
    simpa [prefixWord, tailWord_3713482, baseEnd_3713482] using wordTrace_append hprefix tailTrace_3713482
  have hstable : (prefixWord ++ tailWord_3713482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713482).length < 2 ^ (prefixWord ++ tailWord_3713482).sum := by decide
  have hdescent : baseEnd_3713482 < baseStart_3713482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713529 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 3]
def baseStart_3713529 : Nat := 118140960795 + 3713529 * 2 ^ 59
def prefixEnd_3713529 : Nat := 4983230072969 + 3 ^ 40 * 3713529 * 2
def baseEnd_3713529 : Nat := 1906825301410306534409297

theorem tailTrace_3713529 : CollatzResearch.WordTrace tailWord_3713529 prefixEnd_3713529 1906825301410306534409297 := by
  unfold tailWord_3713529
  simp only [CollatzResearch.WordTrace]
  refine ⟨135443529763526128105455641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90295686509017418736970427 135443529763526128105455641)
  ·
    refine ⟨101582647322644596079091731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135443529763526128105455641 101582647322644596079091731)
    ·
      refine ⟨152373970983966894118637597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101582647322644596079091731 152373970983966894118637597)
      ·
        refine ⟨57140239118987585294489099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152373970983966894118637597 57140239118987585294489099)
        ·
          refine ⟨85710358678481377941733649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57140239118987585294489099 85710358678481377941733649)
          ·
            refine ⟨64282769008861033456300237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85710358678481377941733649 64282769008861033456300237)
            ·
              refine ⟨24106038378322887546112589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64282769008861033456300237 24106038378322887546112589)
              ·
                refine ⟨9039764391871082829792221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24106038378322887546112589 9039764391871082829792221)
                ·
                  refine ⟨3389911646951656061172083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9039764391871082829792221 3389911646951656061172083)
                  ·
                    refine ⟨5084867470427484091758125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389911646951656061172083 5084867470427484091758125)
                    ·
                      refine ⟨1906825301410306534409297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084867470427484091758125 1906825301410306534409297)
                      ·
                        rfl

theorem cell23_3713529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_3713529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713529 prefixEnd_3713529 := by exact prefixLift 3713529
  have htrace : WordTrace (prefixWord ++ tailWord_3713529) baseStart_3713529 baseEnd_3713529 := by
    simpa [prefixWord, tailWord_3713529, baseEnd_3713529] using wordTrace_append hprefix tailTrace_3713529
  have hstable : (prefixWord ++ tailWord_3713529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713529).length < 2 ^ (prefixWord ++ tailWord_3713529).sum := by decide
  have hdescent : baseEnd_3713529 < baseStart_3713529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713562 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_3713562 : Nat := 118140960795 + 3713562 * 2 ^ 59
def prefixEnd_3713562 : Nat := 4983230072969 + 3 ^ 40 * 3713562 * 2
def baseEnd_3713562 : Nat := 635614082090634968432215

theorem tailTrace_3713562 : CollatzResearch.WordTrace tailWord_3713562 prefixEnd_3713562 635614082090634968432215 := by
  unfold tailWord_3713562
  simp only [CollatzResearch.WordTrace]
  refine ⟨33861183343101643685351735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90296488914937716494271293 33861183343101643685351735)
  ·
    refine ⟨50791775014652465528027603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33861183343101643685351735 50791775014652465528027603)
    ·
      refine ⟨76187662521978698292041405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50791775014652465528027603 76187662521978698292041405)
      ·
        refine ⟨28570373445742011859515527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76187662521978698292041405 28570373445742011859515527)
        ·
          refine ⟨42855560168613017789273291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28570373445742011859515527 42855560168613017789273291)
          ·
            refine ⟨64283340252919526683909937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42855560168613017789273291 64283340252919526683909937)
            ·
              refine ⟨48212505189689645012932453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64283340252919526683909937 48212505189689645012932453)
              ·
                refine ⟨9039844723066808439924835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48212505189689645012932453 9039844723066808439924835)
                ·
                  refine ⟨13559767084600212659887253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9039844723066808439924835 13559767084600212659887253)
                  ·
                    refine ⟨635614082090634968432215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13559767084600212659887253 635614082090634968432215)
                    ·
                      rfl

theorem cell23_3713562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_3713562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713562 prefixEnd_3713562 := by exact prefixLift 3713562
  have htrace : WordTrace (prefixWord ++ tailWord_3713562) baseStart_3713562 baseEnd_3713562 := by
    simpa [prefixWord, tailWord_3713562, baseEnd_3713562] using wordTrace_append hprefix tailTrace_3713562
  have hstable : (prefixWord ++ tailWord_3713562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713562).length < 2 ^ (prefixWord ++ tailWord_3713562).sum := by decide
  have hdescent : baseEnd_3713562 < baseStart_3713562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713569 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3713569 : Nat := 118140960795 + 3713569 * 2 ^ 59
def prefixEnd_3713569 : Nat := 4983230072969 + 3 ^ 40 * 3713569 * 2
def baseEnd_3713569 : Nat := 1906845840636486377909113

theorem tailTrace_3713569 : CollatzResearch.WordTrace tailWord_3713569 prefixEnd_3713569 1906845840636486377909113 := by
  unfold tailWord_3713569
  simp only [CollatzResearch.WordTrace]
  refine ⟨135444988683381214936911761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90296659122254143291274507 135444988683381214936911761)
  ·
    refine ⟨101583741512535911202683821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135444988683381214936911761 101583741512535911202683821)
    ·
      refine ⟨38093903067200966701006433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101583741512535911202683821 38093903067200966701006433)
      ·
        refine ⟨28570427300400725025754825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38093903067200966701006433 28570427300400725025754825)
        ·
          refine ⟨21427820475300543769316119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28570427300400725025754825 21427820475300543769316119)
          ·
            refine ⟨32141730712950815653974179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21427820475300543769316119 32141730712950815653974179)
            ·
              refine ⟨48212596069426223480961269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32141730712950815653974179 48212596069426223480961269)
              ·
                refine ⟨4519930881508708451340119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48212596069426223480961269 4519930881508708451340119)
                ·
                  refine ⟨6779896322263062677010179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519930881508708451340119 6779896322263062677010179)
                  ·
                    refine ⟨10169844483394594015515269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6779896322263062677010179 10169844483394594015515269)
                    ·
                      refine ⟨1906845840636486377909113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10169844483394594015515269 1906845840636486377909113)
                      ·
                        rfl

theorem cell23_3713569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3713569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713569 prefixEnd_3713569 := by exact prefixLift 3713569
  have htrace : WordTrace (prefixWord ++ tailWord_3713569) baseStart_3713569 baseEnd_3713569 := by
    simpa [prefixWord, tailWord_3713569, baseEnd_3713569] using wordTrace_append hprefix tailTrace_3713569
  have hstable : (prefixWord ++ tailWord_3713569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713569).length < 2 ^ (prefixWord ++ tailWord_3713569).sum := by decide
  have hdescent : baseEnd_3713569 < baseStart_3713569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713589 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_3713589 : Nat := 118140960795 + 3713589 * 2 ^ 59
def prefixEnd_3713589 : Nat := 4983230072969 + 3 ^ 40 * 3713589 * 2
def baseEnd_3713589 : Nat := 1906856110249576299659021

theorem tailTrace_3713589 : CollatzResearch.WordTrace tailWord_3713589 prefixEnd_3713589 1906856110249576299659021 := by
  unfold tailWord_3713589
  simp only [CollatzResearch.WordTrace]
  refine ⟨135445718143308758352639821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90297145428872505568426547 135445718143308758352639821)
  ·
    refine ⟨50792144303740784382239933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135445718143308758352639821 50792144303740784382239933)
    ·
      refine ⟨19047054113902794143339975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50792144303740784382239933 19047054113902794143339975)
      ·
        refine ⟨28570581170854191215009963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19047054113902794143339975 28570581170854191215009963)
        ·
          refine ⟨42855871756281286822514945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28570581170854191215009963 42855871756281286822514945)
          ·
            refine ⟨32141903817210965116886209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42855871756281286822514945 32141903817210965116886209)
            ·
              refine ⟨24106427862908223837664657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32141903817210965116886209 24106427862908223837664657)
              ·
                refine ⟨18079820897181167878248493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24106427862908223837664657 18079820897181167878248493)
                ·
                  refine ⟨6779932836442937954343185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18079820897181167878248493 6779932836442937954343185)
                  ·
                    refine ⟨5084949627332203465757389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6779932836442937954343185 5084949627332203465757389)
                    ·
                      refine ⟨1906856110249576299659021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5084949627332203465757389 1906856110249576299659021)
                      ·
                        rfl

theorem cell23_3713589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_3713589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713589 prefixEnd_3713589 := by exact prefixLift 3713589
  have htrace : WordTrace (prefixWord ++ tailWord_3713589) baseStart_3713589 baseEnd_3713589 := by
    simpa [prefixWord, tailWord_3713589, baseEnd_3713589] using wordTrace_append hprefix tailTrace_3713589
  have hstable : (prefixWord ++ tailWord_3713589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713589).length < 2 ^ (prefixWord ++ tailWord_3713589).sum := by decide
  have hdescent : baseEnd_3713589 < baseStart_3713589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713592 : List Nat := [2, 1, 2, 1, 4, 1, 4, 8]
def baseStart_3713592 : Nat := 118140960795 + 3713592 * 2 ^ 59
def prefixEnd_3713592 : Nat := 4983230072969 + 3 ^ 40 * 3713592 * 2
def baseEnd_3713592 : Nat := 70624357433019992145241

theorem tailTrace_3713592 : CollatzResearch.WordTrace tailWord_3713592 prefixEnd_3713592 70624357433019992145241 := by
  unfold tailWord_3713592
  simp only [CollatzResearch.WordTrace]
  refine ⟨67722913781148944932499515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90297218374865259909999353 67722913781148944932499515)
  ·
    refine ⟨101584370671723417398749273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67722913781148944932499515 101584370671723417398749273)
    ·
      refine ⟨76188278003792563049061955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101584370671723417398749273 76188278003792563049061955)
      ·
        refine ⟨114282417005688844573592933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76188278003792563049061955 114282417005688844573592933)
        ·
          refine ⟨21427953188566658357548675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114282417005688844573592933 21427953188566658357548675)
          ·
            refine ⟨32141929782849987536323013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21427953188566658357548675 32141929782849987536323013)
            ·
              refine ⟨6026611834284372663060565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32141929782849987536323013 6026611834284372663060565)
              ·
                refine ⟨70624357433019992145241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6026611834284372663060565 70624357433019992145241)
                ·
                  rfl

theorem cell23_3713592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 8].length) (baseStart_3713592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713592 prefixEnd_3713592 := by exact prefixLift 3713592
  have htrace : WordTrace (prefixWord ++ tailWord_3713592) baseStart_3713592 baseEnd_3713592 := by
    simpa [prefixWord, tailWord_3713592, baseEnd_3713592] using wordTrace_append hprefix tailTrace_3713592
  have hstable : (prefixWord ++ tailWord_3713592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713592).length < 2 ^ (prefixWord ++ tailWord_3713592).sum := by decide
  have hdescent : baseEnd_3713592 < baseStart_3713592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713596 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_3713596 : Nat := 118140960795 + 3713596 * 2 ^ 59
def prefixEnd_3713596 : Nat := 4983230072969 + 3 ^ 40 * 3713596 * 2
def baseEnd_3713596 : Nat := 635619901538052590757163

theorem tailTrace_3713596 : CollatzResearch.WordTrace tailWord_3713596 prefixEnd_3713596 635619901538052590757163 := by
  unfold tailWord_3713596
  simp only [CollatzResearch.WordTrace]
  refine ⟨67722986727141699274072321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90297315636188932365429761 67722986727141699274072321)
  ·
    refine ⟨50792240045356274455554241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67722986727141699274072321 50792240045356274455554241)
    ·
      refine ⟨38094180034017205841665681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50792240045356274455554241 38094180034017205841665681)
      ·
        refine ⟨28570635025512904381249261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38094180034017205841665681 28570635025512904381249261)
        ·
          refine ⟨10713988134567339142968473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28570635025512904381249261 10713988134567339142968473)
          ·
            refine ⟨8035491100925504357226355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10713988134567339142968473 8035491100925504357226355)
            ·
              refine ⟨12053236651388256535839533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035491100925504357226355 12053236651388256535839533)
              ·
                refine ⟨4519963744270596200939825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12053236651388256535839533 4519963744270596200939825)
                ·
                  refine ⟨3389972808202947150704869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4519963744270596200939825 3389972808202947150704869)
                  ·
                    refine ⟨635619901538052590757163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389972808202947150704869 635619901538052590757163)
                    ·
                      rfl

theorem cell23_3713596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_3713596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713596 prefixEnd_3713596 := by exact prefixLift 3713596
  have htrace : WordTrace (prefixWord ++ tailWord_3713596) baseStart_3713596 baseEnd_3713596 := by
    simpa [prefixWord, tailWord_3713596, baseEnd_3713596] using wordTrace_append hprefix tailTrace_3713596
  have hstable : (prefixWord ++ tailWord_3713596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713596).length < 2 ^ (prefixWord ++ tailWord_3713596).sum := by decide
  have hdescent : baseEnd_3713596 < baseStart_3713596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713632 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_3713632 : Nat := 118140960795 + 3713632 * 2 ^ 59
def prefixEnd_3713632 : Nat := 4983230072969 + 3 ^ 40 * 3713632 * 2
def baseEnd_3713632 : Nat := 1906878189917719631421323

theorem tailTrace_3713632 : CollatzResearch.WordTrace tailWord_3713632 prefixEnd_3713632 1906878189917719631421323 := by
  unfold tailWord_3713632
  simp only [CollatzResearch.WordTrace]
  refine ⟨67723643241076488348227575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90298190988101984464303433 67723643241076488348227575)
  ·
    refine ⟨101585464861614732522341363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67723643241076488348227575 101585464861614732522341363)
    ·
      refine ⟨152378197292422098783512045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101585464861614732522341363 152378197292422098783512045)
      ·
        refine ⟨57141823984658287043817017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152378197292422098783512045 57141823984658287043817017)
        ·
          refine ⟨42856367988493715282862763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57141823984658287043817017 42856367988493715282862763)
          ·
            refine ⟨64284551982740572924294145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42856367988493715282862763 64284551982740572924294145)
            ·
              refine ⟨48213413987055429693220609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64284551982740572924294145 48213413987055429693220609)
              ·
                refine ⟨36160060490291572269915457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48213413987055429693220609 36160060490291572269915457)
                ·
                  refine ⟨27120045367718679202436593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36160060490291572269915457 27120045367718679202436593)
                  ·
                    refine ⟨20340034025789009401827445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27120045367718679202436593 20340034025789009401827445)
                    ·
                      refine ⟨1906878189917719631421323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20340034025789009401827445 1906878189917719631421323)
                      ·
                        rfl

theorem cell23_3713632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_3713632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713632 prefixEnd_3713632 := by exact prefixLift 3713632
  have htrace : WordTrace (prefixWord ++ tailWord_3713632) baseStart_3713632 baseEnd_3713632 := by
    simpa [prefixWord, tailWord_3713632, baseEnd_3713632] using wordTrace_append hprefix tailTrace_3713632
  have hstable : (prefixWord ++ tailWord_3713632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713632).length < 2 ^ (prefixWord ++ tailWord_3713632).sum := by decide
  have hdescent : baseEnd_3713632 < baseStart_3713632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713653 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3713653 : Nat := 118140960795 + 3713653 * 2 ^ 59
def prefixEnd_3713653 : Nat := 4983230072969 + 3 ^ 40 * 3713653 * 2
def baseEnd_3713653 : Nat := 1906888973011464049258727

theorem tailTrace_3713653 : CollatzResearch.WordTrace tailWord_3713653 prefixEnd_3713653 1906888973011464049258727 := by
  unfold tailWord_3713653
  simp only [CollatzResearch.WordTrace]
  refine ⟨135448052415076897282969613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90298701610051264855313075 135448052415076897282969613)
  ·
    refine ⟨50793019655653836481113605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135448052415076897282969613 50793019655653836481113605)
    ·
      refine ⟨9523691185435094340208801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50793019655653836481113605 9523691185435094340208801)
      ·
        refine ⟨7142768389076320755156601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9523691185435094340208801 7142768389076320755156601)
        ·
          refine ⟨5357076291807240566367451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7142768389076320755156601 5357076291807240566367451)
          ·
            refine ⟨8035614437710860849551177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357076291807240566367451 8035614437710860849551177)
            ·
              refine ⟨6026710828283145637163383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8035614437710860849551177 6026710828283145637163383)
              ·
                refine ⟨9040066242424718455745075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026710828283145637163383 9040066242424718455745075)
                ·
                  refine ⟨13560099363637077683617613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040066242424718455745075 13560099363637077683617613)
                  ·
                    refine ⟨5085037261363904131356605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13560099363637077683617613 5085037261363904131356605)
                    ·
                      refine ⟨1906888973011464049258727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5085037261363904131356605 1906888973011464049258727)
                      ·
                        rfl

theorem cell23_3713653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3713653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713653 prefixEnd_3713653 := by exact prefixLift 3713653
  have htrace : WordTrace (prefixWord ++ tailWord_3713653) baseStart_3713653 baseEnd_3713653 := by
    simpa [prefixWord, tailWord_3713653, baseEnd_3713653] using wordTrace_append hprefix tailTrace_3713653
  have hstable : (prefixWord ++ tailWord_3713653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713653).length < 2 ^ (prefixWord ++ tailWord_3713653).sum := by decide
  have hdescent : baseEnd_3713653 < baseStart_3713653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713710 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3713710 : Nat := 118140960795 + 3713710 * 2 ^ 59
def prefixEnd_3713710 : Nat := 4983230072969 + 3 ^ 40 * 3713710 * 2
def baseEnd_3713710 : Nat := 1906918241408770326245965

theorem tailTrace_3713710 : CollatzResearch.WordTrace tailWord_3713710 prefixEnd_3713710 1906918241408770326245965 := by
  unfold tailWord_3713710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16931266421983799502224323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90300087583913597345196389 16931266421983799502224323)
  ·
    refine ⟨25396899632975699253336485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16931266421983799502224323 25396899632975699253336485)
    ·
      refine ⟨4761918681182943610000591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25396899632975699253336485 4761918681182943610000591)
      ·
        refine ⟨7142878021774415415000887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4761918681182943610000591 7142878021774415415000887)
        ·
          refine ⟨10714317032661623122501331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7142878021774415415000887 10714317032661623122501331)
          ·
            refine ⟨16071475548992434683751997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10714317032661623122501331 16071475548992434683751997)
            ·
              refine ⟨6026803330872163006406999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16071475548992434683751997 6026803330872163006406999)
              ·
                refine ⟨9040204996308244509610499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026803330872163006406999 9040204996308244509610499)
                ·
                  refine ⟨13560307494462366764415749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040204996308244509610499 13560307494462366764415749)
                  ·
                    refine ⟨2542557655211693768327953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13560307494462366764415749 2542557655211693768327953)
                    ·
                      refine ⟨1906918241408770326245965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542557655211693768327953 1906918241408770326245965)
                      ·
                        rfl

theorem cell23_3713710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3713710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713710 prefixEnd_3713710 := by exact prefixLift 3713710
  have htrace : WordTrace (prefixWord ++ tailWord_3713710) baseStart_3713710 baseEnd_3713710 := by
    simpa [prefixWord, tailWord_3713710, baseEnd_3713710] using wordTrace_append hprefix tailTrace_3713710
  have hstable : (prefixWord ++ tailWord_3713710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713710).length < 2 ^ (prefixWord ++ tailWord_3713710).sum := by decide
  have hdescent : baseEnd_3713710 < baseStart_3713710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713756 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3713756 : Nat := 118140960795 + 3713756 * 2 ^ 59
def prefixEnd_3713756 : Nat := 4983230072969 + 3 ^ 40 * 3713756 * 2
def baseEnd_3713756 : Nat := 1906941861518877146270753

theorem tailTrace_3713756 : CollatzResearch.WordTrace tailWord_3713756 prefixEnd_3713756 1906941861518877146270753 := by
  unfold tailWord_3713756
  simp only [CollatzResearch.WordTrace]
  refine ⟨67725904566851872936984561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90301206089135830582646081 67725904566851872936984561)
  ·
    refine ⟨50794428425138904702738421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67725904566851872936984561 50794428425138904702738421)
    ·
      refine ⟨4761977664856772315881727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50794428425138904702738421 4761977664856772315881727)
      ·
        refine ⟨7142966497285158473822591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4761977664856772315881727 7142966497285158473822591)
        ·
          refine ⟨10714449745927737710733887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7142966497285158473822591 10714449745927737710733887)
          ·
            refine ⟨16071674618891606566100831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10714449745927737710733887 16071674618891606566100831)
            ·
              refine ⟨24107511928337409849151247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16071674618891606566100831 24107511928337409849151247)
              ·
                refine ⟨36161267892506114773726871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24107511928337409849151247 36161267892506114773726871)
                ·
                  refine ⟨54241901838759172160590307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36161267892506114773726871 54241901838759172160590307)
                  ·
                    refine ⟨81362852758138758240885461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54241901838759172160590307 81362852758138758240885461)
                    ·
                      refine ⟨1906941861518877146270753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81362852758138758240885461 1906941861518877146270753)
                      ·
                        rfl

theorem cell23_3713756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3713756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713756 prefixEnd_3713756 := by exact prefixLift 3713756
  have htrace : WordTrace (prefixWord ++ tailWord_3713756) baseStart_3713756 baseEnd_3713756 := by
    simpa [prefixWord, tailWord_3713756, baseEnd_3713756] using wordTrace_append hprefix tailTrace_3713756
  have hstable : (prefixWord ++ tailWord_3713756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713756).length < 2 ^ (prefixWord ++ tailWord_3713756).sum := by decide
  have hdescent : baseEnd_3713756 < baseStart_3713756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713769 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 3]
def baseStart_3713769 : Nat := 118140960795 + 3713769 * 2 ^ 59
def prefixEnd_3713769 : Nat := 4983230072969 + 3 ^ 40 * 3713769 * 2
def baseEnd_3713769 : Nat := 1906948536767385595408193

theorem tailTrace_3713769 : CollatzResearch.WordTrace tailWord_3713769 prefixEnd_3713769 1906948536767385595408193 := by
  unfold tailWord_3713769
  simp only [CollatzResearch.WordTrace]
  refine ⟨135452283282656649094192361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90301522188437766062794907 135452283282656649094192361)
  ·
    refine ⟨101589212461992486820644271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135452283282656649094192361 101589212461992486820644271)
    ·
      refine ⟨152383818692988730230966407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101589212461992486820644271 152383818692988730230966407)
      ·
        refine ⟨228575728039483095346449611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152383818692988730230966407 228575728039483095346449611)
        ·
          refine ⟨342863592059224643019674417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228575728039483095346449611 342863592059224643019674417)
          ·
            refine ⟨257147694044418482264755813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342863592059224643019674417 257147694044418482264755813)
            ·
              refine ⟨48215192633328465424641715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257147694044418482264755813 48215192633328465424641715)
              ·
                refine ⟨72322788949992698136962573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48215192633328465424641715 72322788949992698136962573)
                ·
                  refine ⟨27121045856247261801360965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72322788949992698136962573 27121045856247261801360965)
                  ·
                    refine ⟨5085196098046361587755181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27121045856247261801360965 5085196098046361587755181)
                    ·
                      refine ⟨1906948536767385595408193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5085196098046361587755181 1906948536767385595408193)
                      ·
                        rfl

theorem cell23_3713769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_3713769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713769 prefixEnd_3713769 := by exact prefixLift 3713769
  have htrace : WordTrace (prefixWord ++ tailWord_3713769) baseStart_3713769 baseEnd_3713769 := by
    simpa [prefixWord, tailWord_3713769, baseEnd_3713769] using wordTrace_append hprefix tailTrace_3713769
  have hstable : (prefixWord ++ tailWord_3713769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713769).length < 2 ^ (prefixWord ++ tailWord_3713769).sum := by decide
  have hdescent : baseEnd_3713769 < baseStart_3713769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
